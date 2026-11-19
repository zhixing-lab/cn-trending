#!/usr/bin/env python3
"""
GitHub 中文热门：日榜 / 周榜 / 月榜，网站生成器 + 群机器人推送

数据源：GitHub Trending 的 spoken_language_code=zh 筛选（README 为中文的项目）。
GitHub 没有 Trending 的官方 API，所以这里直接解析页面 HTML。

为什么要抓全部语言分榜：
  Trending 的总榜只展示一小部分项目，大量中文热门项目只出现在各编程语言的分榜里
  （实测日榜总榜 20 个，分榜里还有几十个总榜没有的，其中不少涨星比总榜上的还多）。
  所以默认抓“总榜 + 全部语言分榜”（GitHub 列出的所有语言，约 800 多个，包括“未标注语言”），
  按仓库合并去重。语言清单每次从页面上实时读取，GitHub 新增语言也会自动覆盖。
  任何分榜重试后仍抓取失败，都会记录下来，在网站和推送里明确提示“榜单可能不完整”。

新项目榜（--since new）：
  Trending 不收录很多新项目，所以另外用 GitHub 搜索接口抓“近 30 天新建、100 星以上、简介含中文”的仓库，
  并标出疑似批量刷星的仓库（多个账号用同一个词命名、星数全卡在门槛附近，或简介几乎一样）。

全量星数跟踪（--track）：
  Trending 会排除一些项目，所以每天另外把全 GitHub 100 星以上的仓库全部扫一遍，记下中文项目的星数，
  用今天减去 1/7/30 天前的星数算出真实涨星，合并进日榜、周榜、月榜。需要先攒数据：日榜第 2 天、周榜第 8 天、
  月榜第 31 天起生效。
  简介不是中文的中文项目：每天按前一天的涨星挑出最多 300 个简介不是中文的仓库，读 README 判断语言
  （主 README 是英文、但提供中文版 README 的，再看最近的 issue 是不是多用中文），是中文项目的加入跟踪名单
  （见 judge_repo、discover_by_readme）。

其他设计要点：
  1. 按“本期新增 star”排序，不按总 star（页面自带顺序不是按新增排的）
  2. 记住见过的项目，标出“新上榜”，避免每天都是同一批常驻老项目
     （第一次运行只建立基线，不标新，否则整张榜都是“新”）
  3. 可选按“增长率”（新增 / 总 star）排序，把小而新的项目顶上来

依赖：pip install requests beautifulsoup4

常用示例：
  python cn_trending.py                          # 日榜（全部语言分榜）
  python cn_trending.py --since weekly           # 周榜
  python cn_trending.py --since monthly          # 月榜
  python cn_trending.py --since new              # 新项目榜：近 30 天新建、100 星以上（用搜索接口，最好设 GITHUB_TOKEN）
  python cn_trending.py --track --site-dir docs  # 全量星数跟踪：扫全 GitHub 100 星以上的仓库，补全日/周/月榜（约 4 小时）
  python cn_trending.py --lang python --lang go  # 只抓这几个语言分榜（会有遗漏，仅用于快速查看）
  python cn_trending.py --site-dir docs          # 同时生成网站到 docs/
  python cn_trending.py --webhook <URL> --webhook-type feishu
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import datetime as dt
import gzip
import json
import os
import re
import sys
import threading
import time
from pathlib import Path

import requests
from bs4 import BeautifulSoup

TRENDING_URL = "https://github.com/trending/{lang}"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; cn-trending/2.0)",
    "Accept": "text/html",
    "Accept-Language": "en-US,en;q=0.9",  # 保证页面上是 "stars today" 这类英文文案
}
PERIOD_RE = re.compile(r"([\d,]+)\s+stars?\s+(today|this week|this month)")
COLOR_RE = re.compile(r"background-color:\s*([^;]+)")
LANG_HREF_RE = re.compile(r"^/trending/([^/?#]+)(?:\?|$)")
PERIOD_LABEL = {"daily": "今日", "weekly": "本周", "monthly": "本月", "new": "新项目"}
TEMPLATE_PATH = Path(__file__).with_name("site_template.html")
DATA_PLACEHOLDER = "/*__TRENDING_DATA__*/null"
CN_TZ = dt.timezone(dt.timedelta(hours=8))   # 北京时间（中国不实行夏令时）。榜单日期、存档文件名、新项目起点都按它算


def today_cn() -> dt.date:
    return dt.datetime.now(CN_TZ).date()

# 新项目榜：GitHub 搜索接口
SEARCH_URL = "https://api.github.com/search/repositories"
HAN_RE = re.compile(r"[㐀-䶿一-鿿]")
KANA_RE = re.compile(r"[぀-ヿ]")   # 有假名的多半是日文，不算中文
# 搜索接口不返回语言颜色，常见语言用 GitHub（linguist）的配色
LANG_COLORS = {
    "Python": "#3572A5", "JavaScript": "#f1e05a", "TypeScript": "#3178c6", "Go": "#00ADD8",
    "Java": "#b07219", "C++": "#f34b7d", "C": "#555555", "C#": "#178600", "Rust": "#dea584",
    "Kotlin": "#A97BFF", "Swift": "#F05138", "Dart": "#00B4AB", "PHP": "#4F5D95", "Ruby": "#701516",
    "HTML": "#e34c26", "CSS": "#563d7c", "Shell": "#89e051", "Vue": "#41b883", "Lua": "#000080",
    "Jupyter Notebook": "#DA5B0B", "Objective-C": "#438eff", "Svelte": "#ff3e00", "PowerShell": "#012456",
}


# ---------------------------------------------------------------- 抓取

class FetchError(Exception):
    pass


class OutOfTime(FetchError):
    """时间预算用完（或者要等的限流时间超出预算），不再继续。"""


class Pacer:
    """所有线程共用的节流器：两次请求之间至少间隔 interval 秒。"""

    def __init__(self, interval: float):
        self.interval = interval
        self.lock = threading.Lock()
        self.next_at = 0.0

    def wait(self) -> None:
        with self.lock:
            now = time.monotonic()
            at = max(now, self.next_at)
            self.next_at = at + self.interval
        if at > now:
            time.sleep(at - now)

    def pause(self, seconds: float) -> None:
        """遇到限流时让所有线程一起暂停。"""
        with self.lock:
            self.next_at = max(self.next_at, time.monotonic() + seconds)


_local = threading.local()
_pacer = Pacer(0.25)


def _session() -> requests.Session:
    s = getattr(_local, "session", None)
    if s is None:
        s = _local.session = requests.Session()
        s.headers.update(HEADERS)
    return s


def fetch_html(lang: str, since: str, retries: int = 6) -> str | None:
    """
    抓一个 Trending 页面。返回 HTML；该语言分榜不存在（404）时返回 None。
    429 限流按 Retry-After 等待（没有就逐次加长），5xx 和网络错误指数退避；重试用完抛 FetchError。
    """
    url = TRENDING_URL.format(lang=lang)
    params = {"since": since, "spoken_language_code": "zh"}
    last = ""
    for attempt in range(1, retries + 1):
        _pacer.wait()
        try:
            r = _session().get(url, params=params, timeout=30)
        except requests.RequestException as e:
            last = str(e)
            time.sleep(min(2 ** attempt, 60))
            continue
        if r.status_code == 200:
            return r.text
        if r.status_code == 404:
            return None
        last = f"HTTP {r.status_code}"
        if r.status_code == 429:
            ra = r.headers.get("Retry-After", "")
            wait = int(ra) if ra.isdigit() else 30 * attempt
            print(f"[warn] 被限流，全部暂停 {wait} 秒（{lang or 'all'}）", file=sys.stderr)
            _pacer.pause(wait)
        else:
            time.sleep(min(2 ** attempt, 60))
    raise FetchError(f"{lang or 'all'}: {last}")


# ---------------------------------------------------------------- 解析

def _int(text: str | None) -> int:
    digits = re.sub(r"[^\d]", "", text or "")
    return int(digits) if digits else 0


def parse_trending(html: str) -> list[dict]:
    """解析 Trending 页面，返回项目列表。尽量只依赖稳定的结构（链接 href、itemprop），少依赖 CSS 类名。"""
    soup = BeautifulSoup(html, "html.parser")
    repos = []
    for art in soup.select("article.Box-row"):
        link = art.select_one("h2 a[href]")
        if not link:
            continue
        full_name = link["href"].strip("/")
        desc_el = art.select_one("p")
        lang_el = art.select_one('[itemprop="programmingLanguage"]')
        color_el = art.select_one(".repo-language-color[style]")
        color_m = COLOR_RE.search(color_el["style"]) if color_el else None
        stars_el = art.select_one('a[href$="/stargazers"]')
        forks_el = art.select_one('a[href$="/forks"]')
        m = PERIOD_RE.search(" ".join(art.get_text(" ").split()))
        repos.append({
            "repo": full_name,
            "url": f"https://github.com/{full_name}",
            "desc": " ".join(desc_el.get_text(" ").split()) if desc_el else "",
            "language": lang_el.get_text(strip=True) if lang_el else "",
            "lang_color": color_m.group(1).strip() if color_m else "",
            "stars": _int(stars_el.get_text() if stars_el else None),
            "forks": _int(forks_el.get_text() if forks_el else None),
            "period_stars": _int(m.group(1)) if m else 0,
        })
    return repos


def parse_language_slugs(html: str) -> list[str]:
    """从 Trending 页面的语言下拉菜单里读出全部语言分榜（含 unknown = 未标注语言）。"""
    soup = BeautifulSoup(html, "html.parser")
    slugs = []
    for a in soup.select('a[href^="/trending/"]'):
        m = LANG_HREF_RE.match(a["href"])
        if m and m.group(1) != "developers" and m.group(1) not in slugs:
            slugs.append(m.group(1))
    return slugs


def collect(since: str, langs: list[str] | None = None, workers: int = 4) -> tuple[list[dict], dict]:
    """
    抓取并合并：总榜 + 语言分榜。langs 为空时抓全部语言分榜。
    返回 (项目列表, 覆盖情况)。
    """
    overall = fetch_html("", since)
    if overall is None:
        raise FetchError("总榜返回 404")
    merged: dict[str, dict] = {}
    found_in: dict[str, set] = {}

    def add(items: list[dict], source: str) -> None:
        for it in items:
            old = merged.get(it["repo"])
            if not old or it["period_stars"] > old["period_stars"]:
                merged[it["repo"]] = it
            found_in.setdefault(it["repo"], set()).add(source)

    overall_items = parse_trending(overall)
    add(overall_items, "(all)")
    slugs = langs if langs else parse_language_slugs(overall)
    if not langs and (not overall_items or len(slugs) < 50):
        # 页面能打开却解析不出项目或语言清单，多半是 GitHub 改版了：直接报错，别静默生成残缺榜单
        raise RuntimeError(f"Trending 页面解析异常（项目 {len(overall_items)} 个，语言 {len(slugs)} 个），可能是页面结构变了")

    failed: list[str] = []
    nonempty = 0
    done = 0

    def job(slug: str):
        return slug, fetch_html(slug, since)

    pending = list(slugs)
    for round_no in (1, 2):  # 第二轮只重抓第一轮失败的分榜
        failed = []
        with cf.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = [ex.submit(job, s) for s in pending]
            for f in cf.as_completed(futs):
                try:
                    slug, html = f.result()
                except FetchError as e:
                    failed.append(str(e).split(":")[0])
                    continue
                done += 1
                items = parse_trending(html) if html else []
                if items:
                    nonempty += 1
                    add(items, slug)
                if done % 100 == 0:
                    print(f"[info] {since}：已抓 {done}/{len(slugs)} 个分榜，累计 {len(merged)} 个项目", file=sys.stderr)
        if not failed:
            break
        if round_no == 1:
            print(f"[warn] {len(failed)} 个分榜失败，60 秒后重试", file=sys.stderr)
            time.sleep(60)
            pending = failed

    coverage = {
        "pages": len(slugs) + 1,                 # 分榜数 + 总榜
        "ok": len(slugs) + 1 - len(failed),
        "failed": sorted(failed),
        "nonempty_lang_pages": nonempty,
        "overall_count": len(overall_items),
        "only_in_lang_pages": sum(1 for v in found_in.values() if "(all)" not in v),
        "full_sweep": not langs,
    }
    return list(merged.values()), coverage


# ---------------------------------------------------------------- 新项目榜（搜索接口）
#
# GitHub Trending 不收录很多新项目（实测一个 10 月 25 日才建、一个月涨了 2.7 万星的中文项目，
# 在所有 Trending 榜单上都找不到），所以新项目单独用搜索接口抓：
#   近 N 天新建、星数达标的全部仓库 → 简介含中文的算中文项目 → 标出疑似批量刷星的仓库。
# 搜索接口每个查询最多返回 1000 条，所以按天切时间段，某段超过 1000 条再对半切，保证不漏。

_search_pacer = Pacer(2.05)  # 带 token 每分钟最多 30 次搜索，这里每分钟约 29 次；没 token 时在 main 里改成每分钟不到 10 次


def is_chinese(text: str | None) -> bool:
    t = text or ""
    return len(HAN_RE.findall(t)) >= 2 and not KANA_RE.search(t)


def search_page(query: str, page: int, token: str = "", retries: int = 6) -> dict:
    """调一次搜索接口。限流时按响应头等待；结果不完整（incomplete_results）时重试。"""
    headers = {"Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28",
               "User-Agent": HEADERS["User-Agent"]}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    params = {"q": query, "sort": "stars", "order": "desc", "per_page": 100, "page": page}
    last = ""
    for attempt in range(1, retries + 1):
        _search_pacer.wait()
        try:
            r = _session().get(SEARCH_URL, params=params, headers=headers, timeout=30)
        except requests.RequestException as e:
            last = str(e)
            time.sleep(min(2 ** attempt, 60))
            continue
        if r.status_code == 200:
            data = r.json()
            if data.get("incomplete_results") and attempt < retries:
                last = "incomplete_results"
                time.sleep(3 * attempt)
                continue
            return data
        last = f"HTTP {r.status_code}"
        if r.status_code in (403, 429):
            reset = r.headers.get("X-RateLimit-Reset", "")
            if r.headers.get("X-RateLimit-Remaining") == "0" and reset.isdigit():
                wait = max(1, int(reset) - int(time.time()) + 2)
            else:
                ra = r.headers.get("Retry-After", "")
                wait = int(ra) if ra.isdigit() else 30 * attempt
            print(f"[warn] 搜索接口限流，暂停 {wait} 秒", file=sys.stderr)
            _search_pacer.pause(wait)
        else:
            time.sleep(min(2 ** attempt, 60))
    raise FetchError(f"search: {last}")


def _iso(t: dt.datetime) -> str:
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def search_window(a: dt.datetime, b: dt.datetime, min_stars: int, token: str, stats: dict) -> list[dict]:
    """抓 [a, b) 时间段内新建的仓库；超过 1000 条就对半切开分别抓。"""
    query = f"created:{_iso(a)}..{_iso(b - dt.timedelta(seconds=1))} stars:>={min_stars}"
    first = search_page(query, 1, token)
    stats["queries"] += 1
    total = first.get("total_count", 0)
    if total > 1000 and (b - a) > dt.timedelta(minutes=2):
        mid = a + (b - a) / 2
        mid = mid.replace(microsecond=0)
        return search_window(a, mid, min_stars, token, stats) + search_window(mid, b, min_stars, token, stats)
    items = list(first.get("items", []))
    label = a.astimezone(CN_TZ).strftime("%Y-%m-%d %H:%M") + " 北京时间"
    if first.get("incomplete_results"):
        stats["incomplete"].append(label)
    for page in range(2, (min(total, 1000) + 99) // 100 + 1):
        data = search_page(query, page, token)
        stats["queries"] += 1
        items += data.get("items", [])
        if data.get("incomplete_results"):
            stats["incomplete"].append(label)
    stats["windows"] += 1
    if total > 1000:
        stats["capped"].append(label)   # 两分钟内新建超过 1000 个达标仓库，几乎不可能，但要如实记下
    return items


def flag_batches(items: list[dict], min_stars: int) -> None:
    """
    标出疑似批量刷星的仓库（r["batch"] = True）。两条规则：
      1. 同一个词出现在 ≥5 个不同账号的仓库名或简介里，而这些仓库的星数全都卡在门槛附近（≤ 门槛 × 1.5）。
         这个统计在全部搜索结果（中外项目都算）上做，常见词总会出现在高星项目里，不会误伤。
      2. ≥3 个不同账号的仓库简介几乎一样（字符三元组相似度 ≥ 0.5），通常是批量复制或镜像。
    """
    def words(r):
        name = {t for t in re.split(r"[^a-z0-9]+", r["repo"].split("/")[1].lower()) if len(t) >= 5}
        return name | set(re.findall(r"[a-z][a-z0-9]{5,}", (r["desc"] or "").lower()))

    owners: dict[str, set] = {}
    members: dict[str, list] = {}
    for i, r in enumerate(items):
        r.setdefault("batch", False)
        for w in words(r):
            owners.setdefault(w, set()).add(r["repo"].split("/")[0])
            members.setdefault(w, []).append(i)
    cap = min_stars * 1.5
    for w, o in owners.items():
        if len(o) >= 5 and max(items[i]["stars"] for i in members[w]) <= cap:
            for i in members[w]:
                items[i]["batch"] = True

    def grams_of(s: str) -> set:
        s = re.sub(r"\s+", "", s.lower())
        return {s[k:k + 3] for k in range(len(s) - 2)}

    cn = [i for i, r in enumerate(items) if r.get("chinese") and r["desc"]]
    grams = {i: grams_of(items[i]["desc"]) for i in cn}
    parent = {i: i for i in cn}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for n, i in enumerate(cn):
        for j in cn[n + 1:]:
            if items[i]["repo"].split("/")[0] == items[j]["repo"].split("/")[0]:
                continue
            a, b = grams[i], grams[j]
            if a and b and len(a & b) / len(a | b) >= 0.5:
                parent[find(i)] = find(j)
    groups: dict[int, list] = {}
    for i in cn:
        groups.setdefault(find(i), []).append(i)
    for g in groups.values():
        if len({items[i]["repo"].split("/")[0] for i in g}) >= 3:
            for i in g:
                items[i]["batch"] = True


def _cn_midnight(d: dt.date) -> dt.datetime:
    """北京时间某天 0 点，换成 UTC（搜索接口用 UTC 时间）。"""
    return dt.datetime.combine(d, dt.time(0, 0), tzinfo=CN_TZ).astimezone(dt.timezone.utc)


def collect_new(days: int = 30, min_stars: int = 100, token: str = "",
                now: dt.datetime | None = None, readme_cache: dict | None = None,
                deadline: float = float("inf")) -> tuple[list[dict], dict]:
    """
    近 days 天新建、星数 ≥ min_stars 的中文项目。返回 (项目列表, 覆盖情况)。
    起点按北京时间整天算：今天（北京时间）往前推 days 天的 0 点，例如 11 月 19 日运行就从 10 月 20 日 0 点算起，
    相当于搜索条件 created:>=那一天（北京时间）。
    简介含中文的直接算；给了 readme_cache 时，简介不是中文的也逐个用 judge_repo 看 README（结果记进 readme_cache，
    下次不重复查），到 deadline（time.monotonic）还没查完的留到下次。
    """
    now = (now or dt.datetime.now(dt.timezone.utc)).replace(second=0, microsecond=0)
    start_day = now.astimezone(CN_TZ).date() - dt.timedelta(days=days)
    start = _cn_midnight(start_day)
    stats = {"queries": 0, "windows": 0, "incomplete": [], "capped": []}
    raw: dict[str, dict] = {}
    failed: list[str] = []
    a = start
    while a < now:
        # 按北京时间自然日切段（最后一段是今天，不满一天），失败时能准确说出是哪一天
        day = a.astimezone(CN_TZ).date()
        b = min(_cn_midnight(day + dt.timedelta(days=1)), now)
        try:
            for it in search_window(a, b, min_stars, token, stats):
                raw[it["full_name"]] = it
        except FetchError as e:
            failed.append(f"{day}（北京时间，{e}）")
        print(f"[info] new：已搜到 {day}（北京时间），累计 {len(raw)} 个新仓库", file=sys.stderr)
        a = b

    items = []
    for it in raw.values():
        created = dt.datetime.strptime(it["created_at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
        age = max(1.0, (now - created).total_seconds() / 86400)
        lang = it.get("language") or ""
        items.append({
            "repo": it["full_name"],
            "url": it.get("html_url") or f"https://github.com/{it['full_name']}",
            "desc": " ".join((it.get("description") or "").split()),
            "language": lang,
            "lang_color": LANG_COLORS.get(lang, ""),
            "stars": it.get("stargazers_count", 0),
            "forks": it.get("forks_count", 0),
            "period_stars": it.get("stargazers_count", 0),   # 都是近期新建的，总星数就是这段时间涨的
            "created": created.astimezone(CN_TZ).strftime("%Y-%m-%d"),   # 北京时间的建库日期
            "age_days": round(age, 1),
            "per_day": round(it.get("stargazers_count", 0) / age, 1),
            "chinese": is_chinese(it.get("description")),
        })
    flag_batches(items, min_stars)
    readme = check_new_readmes(items, readme_cache, token, now.astimezone(CN_TZ).date(), deadline) \
        if readme_cache is not None else None
    cn = [r for r in items if r["chinese"]]
    for r in cn:
        r.pop("chinese", None)
    coverage = {
        "kind": "search",
        "full_sweep": True,
        "days": days,
        "start": start_day.isoformat(),          # 起点（北京时间当天 0 点）
        "min_stars": min_stars,
        "windows": stats["windows"],
        "queries": stats["queries"],
        "failed": failed + [f"{w}（结果不完整）" for w in stats["incomplete"]] + [f"{w}（超过 1000 条上限）" for w in stats["capped"]],
        "candidates": len(items),
        "chinese": len(cn),
        "batch": sum(1 for r in cn if r["batch"]),
        # 整个候选池里疑似批量刷星的仓库（包括简介不是中文的），给靠 README 补进来的项目用
        "batch_repos": sorted(r["repo"] for r in items if r["batch"]),
    }
    if readme is not None:
        coverage["readme"] = readme
    return cn, coverage


def check_new_readmes(items: list[dict], cache: dict, token: str, today: dt.date, deadline: float) -> dict:
    """
    新项目榜：简介不是中文的候选逐个用 judge_repo 判断，是中文项目的标上 chinese 和 readme_zh。
    cache = {仓库名: {"d": 查的日期, "zh": 是否中文, "r": 几天后再查, "k": 依据}}，在原地更新。
    再查的间隔：认定是中文的 30 天；附了中文版 README 但 issue 太少、暂时判断不了的每天再查（issue 多了就能认出来）；
    其他 7 天（新项目的 README 变化快）。按日均星从高到低查，到 deadline 还没查完的留到下次。
    """
    t = today.isoformat()
    for k in [k for k, v in cache.items() if v.get("d", "") <= (today - dt.timedelta(days=v.get("r", 7))).isoformat()]:
        del cache[k]
    todo = sorted((r for r in items if not r["chinese"]), key=lambda r: -r["per_day"])
    info = {"candidates": len(todo), "checked": 0, "zh": 0, "errors": 0, "pending": 0, "stopped": ""}
    for r in todo:
        c = cache.get(r["repo"])
        if c is None and not info["stopped"]:
            try:
                zh, how, recheck = judge_repo(r["repo"], token, deadline)
            except OutOfTime as e:
                info["stopped"] = str(e)
            except FetchError:
                info["errors"] += 1
            else:
                info["checked"] += 1
                c = cache[r["repo"]] = {"d": t, "zh": zh, "r": 30 if zh else (1 if recheck < README_RECHECK_DAYS else 7)} \
                    | ({"k": how} if how else {})
        if c is None:
            info["pending"] += 1
        elif c["zh"]:
            r["chinese"] = r["readme_zh"] = True
            info["zh"] += 1
    if info["checked"] or info["pending"]:
        print(f"[info] new：简介不是中文的 {info['candidates']} 个，本次看了 {info['checked']} 个的 README，"
              f"认出中文项目共 {info['zh']} 个，还剩 {info['pending']} 个没看"
              f"{('（' + info['stopped'] + '）') if info['stopped'] else ''}", file=sys.stderr)
    return info


# ---------------------------------------------------------------- 全量星数跟踪（--track）
#
# Trending 会排除一些项目（原因不公开），只靠它做不到全面。所以另外每天把全 GitHub 达到门槛（默认 100 星）的
# 仓库全部扫一遍，挑出中文项目记下当天星数；用今天减去 1 天、7 天、30 天前的星数，得到真实的日、周、月涨星，
# 再和 Trending 的结果合并。历史星数存在单独的 star-history 分支里（每次覆盖，仓库不会越变越大）。

PERIOD_DAYS = {"daily": 1, "weekly": 7, "monthly": 30}
MAX_STARS = 10_000_000
EPOCH = dt.datetime(2007, 10, 1, tzinfo=dt.timezone.utc)   # 早于 GitHub 上线
KEEP_SNAPSHOTS = 31


def enumerate_repos(min_stars: int, token: str, deadline: float, keep: set, stats: dict,
                    now: dt.datetime | None = None) -> dict[str, dict]:
    """
    搜全 GitHub 星数 ≥ min_stars 的仓库（含 fork），只保留中文项目（简介含中文，或在 keep 里）。
    每个查询最多拿 1000 条：先按星数区间对半切；单个星数仍超过 1000 条，再按建库时间对半切。
    超过 deadline（time.monotonic）就停，没扫完的区间记进 stats["unfinished"]。
    """
    now = now or dt.datetime.now(dt.timezone.utc)
    found: dict[str, dict] = {}
    pending = [(min_stars, MAX_STARS, None, None)]
    while pending:
        lo, hi, a, b = pending.pop()
        label = f"{lo}~{hi} 星" + (f"，{a.astimezone(CN_TZ):%Y-%m-%d %H:%M} 起建库" if a else "")
        if time.monotonic() > deadline:
            stats["unfinished"].append(label)
            continue
        query = f"stars:{lo}..{hi} fork:true" + (f" created:{_iso(a)}..{_iso(b - dt.timedelta(seconds=1))}" if a else "")
        try:
            first = search_page(query, 1, token)
        except FetchError as e:
            stats["failed"].append(f"{label}（{e}）")
            continue
        stats["queries"] += 1
        total = first.get("total_count", 0)
        if total > 1000:
            if hi > lo:
                mid = (lo + hi) // 2
                pending += [(mid + 1, hi, a, b), (lo, mid, a, b)]
                continue
            a0, b0 = a or EPOCH, b or now
            if b0 - a0 > dt.timedelta(minutes=2):
                # 一次切成足够多段（每段约 800 条），比反复对半切少浪费查询
                parts = min(16, max(2, -(-total // 800)))
                cuts = [(a0 + (b0 - a0) * k / parts).replace(microsecond=0) for k in range(parts + 1)]
                cuts[-1] = b0
                pending += [(lo, hi, cuts[k], cuts[k + 1]) for k in reversed(range(parts))]
                continue
            stats["capped"].append(label)
        items = list(first.get("items", []))
        if first.get("incomplete_results"):
            stats["incomplete"].append(label)
        for page in range(2, (min(total, 1000) + 99) // 100 + 1):
            if time.monotonic() > deadline:
                stats["unfinished"].append(f"{label}（第 {page} 页起）")
                break
            try:
                data = search_page(query, page, token)
            except FetchError as e:
                stats["failed"].append(f"{label} 第 {page} 页（{e}）")
                break
            stats["queries"] += 1
            items += data.get("items", [])
            if data.get("incomplete_results"):
                stats["incomplete"].append(label)
        for it in items:
            stats["scanned_ids"].add(it["id"])
            name = it["full_name"]
            rid = str(it["id"])
            desc = " ".join((it.get("description") or "").split())
            if is_chinese(desc) or name in keep or rid in keep:
                found[rid] = {
                    "repo": name,
                    "url": it.get("html_url") or f"https://github.com/{name}",
                    "desc": desc,
                    "language": it.get("language") or "",
                    "lang_color": LANG_COLORS.get(it.get("language") or "", ""),
                    "stars": it.get("stargazers_count", 0),
                    "forks": it.get("forks_count", 0),
                    "created_at": it.get("created_at", ""),
                }
            elif "others" in stats:
                # 简介不是中文的仓库也简单记一下（用元组省内存），用来找“简介英文、README 中文”的项目
                stats["others"][rid] = (name, desc, it.get("language") or "", it.get("stargazers_count", 0),
                                        it.get("forks_count", 0), it.get("created_at", ""))
        if stats["queries"] - stats.get("printed", 0) >= 200:
            stats["printed"] = stats["queries"]
            print(f"[info] track：已查询 {stats['queries']} 次，扫描 {len(stats['scanned_ids'])} 个仓库，"
                  f"其中中文 {len(found)} 个", file=sys.stderr)
    return found


# ---------------------------------------------------------------- README 中文检测
#
# 全量跟踪靠简介判断中文，但有些中文项目简介写英文（README 是中文，或者默认 README 是英文、另有中文版），
# Trending 又没收录它们时就会漏掉。所以每天把简介不是中文的仓库的星数也存一份（all_stars.json.gz），
# 第二天按这一天的涨星排序，检查涨得最多的一批（judge_repo）：是中文项目就永久加入跟踪名单；不是的过一段时间再查。

README_URL = "https://api.github.com/repos/{name}/readme"
ISSUES_URL = "https://api.github.com/repos/{name}/issues?state=all&per_page=50"
README_MAX_BYTES = 300_000
README_RECHECK_DAYS = 30
ALL_STARS_FILE = "all_stars.json.gz"
_readme_pacer = Pacer(0.4)
_FENCE_RE = re.compile(r"```.*?```|~~~.*?~~~", re.S)
_TAG_RE = re.compile(r"<[^>]*>")
_LINK_RE = re.compile(r"https?://\S+|\]\([^)]*\)")
_LATIN_RE = re.compile(r"[A-Za-z]")
_ZH_DOC_RE = re.compile(r"中文|简体|簡體|繁體|繁体")
_LINK_TARGET_RE = re.compile(r"""(?:href=["']|\]\()\s*([^"')\s]+)""", re.I)
_ZH_FILE_RE = re.compile(r"(?:^|[/_.\-])(?:zh|cn|chs|cht|chinese|zh[-_]?(?:cn|hans|hant|tw|hk))(?:[/_.\-]|$)", re.I)


def readme_is_chinese(text: str | None) -> bool:
    """
    README 正文是不是中文：去掉代码块、HTML 标签和链接后，汉字至少 100 个，
    且汉字占比够高（汉字数 ≥ 0.3 × (汉字数 + 英文字母数 / 4)，大致相当于中文内容不少于英文的一半）；假名多的算日文。
    中英双语写在同一个 README 里的算中文；英文 README 只放个“中文文档”链接的不算。
    """
    t = _LINK_RE.sub(" ", _TAG_RE.sub(" ", _FENCE_RE.sub(" ", text or "")))
    han = len(HAN_RE.findall(t))
    kana = len(KANA_RE.findall(t))
    latin = len(_LATIN_RE.findall(t))
    return han >= 100 and kana * 5 < han and han >= 0.3 * (han + latin / 4)


def _api_get(url: str, token: str, deadline: float, accept: str, max_bytes: int = README_MAX_BYTES,
             retries: int = 4) -> bytes | None:
    """调一次 GitHub REST 接口（README、issue 用）。返回内容（最多 max_bytes）；不存在或不可访问返回 None；读不到抛 FetchError。"""
    headers = {"Accept": accept, "X-GitHub-Api-Version": "2022-11-28", "User-Agent": HEADERS["User-Agent"]}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    last = ""
    for attempt in range(1, retries + 1):
        if time.monotonic() > deadline:
            raise OutOfTime("时间用完")
        _readme_pacer.wait()
        try:
            with _session().get(url, headers=headers, timeout=30, stream=True) as r:
                if r.status_code == 200:
                    buf = b""
                    for chunk in r.iter_content(65536):
                        buf += chunk
                        if len(buf) >= max_bytes:
                            break
                    return buf[:max_bytes]
                last = f"HTTP {r.status_code}"
                ra = r.headers.get("Retry-After", "")
                reset = r.headers.get("X-RateLimit-Reset", "")
                limited = r.status_code == 429 or (r.status_code == 403 and (
                    r.headers.get("X-RateLimit-Remaining") == "0" or ra.isdigit() or "rate limit" in r.text.lower()))
                if r.status_code in (404, 410, 451) or (r.status_code == 403 and not limited):
                    return None   # 没有 README、issue 关了，或仓库被封禁、不可访问
                if limited:
                    if r.headers.get("X-RateLimit-Remaining") == "0" and reset.isdigit():
                        wait = max(1, int(reset) - int(time.time()) + 2)
                    else:
                        wait = int(ra) if ra.isdigit() else 30 * attempt
                    if time.monotonic() + wait > deadline:
                        raise OutOfTime(f"接口限流，要等 {wait} 秒，时间不够")
                    print(f"[warn] GitHub 接口限流，暂停 {wait} 秒", file=sys.stderr)
                    _readme_pacer.pause(wait)
                    continue
        except requests.RequestException as e:
            last = str(e)
        time.sleep(min(2 ** attempt, 30))
    raise FetchError(f"{url}: {last}")


def fetch_readme(name: str, token: str, deadline: float) -> str:
    """仓库默认分支的 README 原文（最多 300KB），没有就返回 ""。"""
    body = _api_get(README_URL.format(name=name), token, deadline, "application/vnd.github.raw+json")
    return (body or b"").decode("utf-8", "ignore")


def fetch_issue_titles(name: str, token: str, deadline: float) -> list[str]:
    """最近 30 个 issue 的标题（不含 PR；包括已关闭的）。issue 关了就返回空列表。"""
    body = _api_get(ISSUES_URL.format(name=name), token, deadline, "application/vnd.github+json", 2_000_000)
    try:
        items = json.loads(body or b"[]")
    except ValueError:
        return []
    return [it.get("title") or "" for it in items if isinstance(it, dict) and "pull_request" not in it][:30]


def readme_offers_chinese(text: str | None) -> bool:
    """README 里有没有提供中文版：出现“中文/简体/繁體”等字样，或者链接到 README_zh.md、docs/zh/README.md 这类文件。"""
    t = text or ""
    if _ZH_DOC_RE.search(t):
        return True
    for target in _LINK_TARGET_RE.findall(t):
        m = re.match(r"(.*)\.md(?:#.*)?$", target, re.I)
        if m and _ZH_FILE_RE.search("/".join(m.group(1).split("/")[-2:])):
            return True
    return False


def judge_repo(name: str, token: str, deadline: float) -> tuple[bool, str, int]:
    """
    判断一个简介不是中文的仓库是不是中文项目。返回 (是否中文, 依据, 多少天后可以再查)。
      1. 主 README 是中文 → 是（依据 readme）
      2. 主 README 是英文，但提供了中文版 README，而且最近的 issue 多用中文（至少 2 个、占 20% 以上）→ 是（依据 issues）
         这类是中国团队做的、默认展示英文 README 的项目，GitHub Trending 的中文榜也把它们算作中文项目
      3. 其他 → 不是。issue 太少（不到 10 个）判断不了的，7 天后再查；其余 30 天后再查
    """
    text = fetch_readme(name, token, deadline)
    if readme_is_chinese(text):
        return True, "readme", README_RECHECK_DAYS
    if not readme_offers_chinese(text):
        return False, "", README_RECHECK_DAYS
    titles = fetch_issue_titles(name, token, deadline)
    zh = sum(1 for x in titles if is_chinese(x))
    if zh >= 2 and zh >= 0.2 * len(titles):
        return True, "issues", README_RECHECK_DAYS
    return False, "", 7 if len(titles) < 10 else README_RECHECK_DAYS


def load_all_stars(path: Path) -> dict:
    try:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_all_stars(path: Path, today: dt.date, min_stars: int, complete: bool, found: dict, others: dict) -> None:
    stars = {rid: r["stars"] for rid, r in found.items()}
    stars.update({rid: o[3] for rid, o in others.items()})
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(path, "wt", encoding="utf-8") as f:
        json.dump({"date": today.isoformat(), "min_stars": min_stars, "complete": complete, "stars": stars},
                  f, separators=(",", ":"))


def discover_by_readme(hist: dict, others: dict, prev: dict, today: dt.date, token: str,
                       limit: int, deadline: float) -> tuple[dict, dict]:
    """
    others：今天扫描到、简介不是中文的仓库 {id: (名字, 简介, 语言, 星数, fork 数, 建库时间)}
    prev：  前一天全部仓库的星数（load_all_stars 读出来的）
    按前一天到今天的涨星排序，用 judge_repo 判断前 limit 个（最近查过的跳过）是不是中文项目。
    返回 (认出来的中文项目 {id: 和 enumerate_repos 一样的格式}, 统计)。
    """
    cache = hist.setdefault("readme", {})
    t = today.isoformat()
    for k in [k for k, v in cache.items()
              if v.get("d", "") <= (today - dt.timedelta(days=v.get("r", README_RECHECK_DAYS))).isoformat()]:
        del cache[k]
    info = {"checked": 0, "added": 0, "by_issues": 0, "errors": 0, "candidates": 0, "stopped": "", "min_gain": None}
    if prev.get("date") != (today - dt.timedelta(days=1)).isoformat():
        info["stopped"] = "没有前一天的全部仓库星数，明天开始检查"
        return {}, info
    pstars = prev.get("stars", {})
    floor = prev.get("min_stars", 0) - 1 if prev.get("complete") else None
    cands = []
    for rid, o in others.items():
        if rid in cache:
            continue
        p = pstars.get(rid)
        if p is None:
            if floor is None:
                continue      # 前一天的扫描不完整：没记录不代表当时不到门槛，算不出涨星
            p = floor         # 前一天还不到门槛：涨星至少是 今天 − (门槛 − 1)
        if o[3] - p > 0:
            cands.append((o[3] - p, rid))
    cands.sort(reverse=True)
    info["candidates"] = len(cands)
    out: dict[str, dict] = {}
    for gain, rid in cands[:limit]:
        name, desc, lang, stars, forks, created = others[rid]
        try:
            zh, how, recheck = judge_repo(name, token, deadline)
        except OutOfTime as e:
            info["stopped"] = str(e)
            break
        except FetchError:
            info["errors"] += 1
            continue
        info["checked"] += 1
        info["min_gain"] = gain
        cache[rid] = {"d": t, "zh": zh, "r": recheck} | ({"k": how} if how else {})
        if zh:
            info["by_issues"] += how == "issues"
            out[rid] = {"repo": name, "url": f"https://github.com/{name}", "desc": desc, "language": lang,
                        "lang_color": LANG_COLORS.get(lang, ""), "stars": stars, "forks": forks, "created_at": created}
    info["added"] = len(out)
    return out, info


def update_history(hist: dict, today: dt.date, min_stars: int, complete: bool, found: dict) -> dict:
    """
    把今天的星数写进历史。hist = {"snapshots": [{"date", "min_stars", "complete"}], "repos": {id: {"n": 名字, "s": [星数或 None]}}}
    同一天重跑会覆盖当天那一列；只保留最近 KEEP_SNAPSHOTS 天。
    """
    snaps = hist.setdefault("snapshots", [])
    repos = hist.setdefault("repos", {})
    t = today.isoformat()
    meta = {"date": t, "min_stars": min_stars, "complete": complete}
    if snaps and snaps[-1]["date"] == t:
        idx = len(snaps) - 1
        snaps[idx] = meta
    else:
        snaps.append(meta)
        idx = len(snaps) - 1
        for r in repos.values():
            r["s"].append(None)
    for rid, r in found.items():
        entry = repos.setdefault(rid, {"n": r["repo"], "s": [None] * len(snaps)})
        entry["n"] = r["repo"]
        entry["s"][idx] = r["stars"]
    drop = max(0, len(snaps) - KEEP_SNAPSHOTS)
    if drop:
        del snaps[:drop]
        for r in repos.values():
            del r["s"][:drop]
    for rid in [k for k, r in repos.items() if all(v is None for v in r["s"])]:
        del repos[rid]
    return hist


def tracked_gains(hist: dict, found: dict, today: dt.date, period: str, top: int = 200) -> tuple[list[dict], dict]:
    """
    算某个周期的涨星。基准是 today 往前 N 天那一天的快照：
      - 那天有记录：涨星 = 今天 − 那天（准确）
      - 那天还没建库：涨星 = 今天的星数（准确，全是这段时间涨的）
      - 那天没记录，但那次快照是完整的：说明当时不到门槛，涨星至少 = 今天 − (门槛 − 1)，标 approx
    返回 (涨星最多的 top 个, 状态)。
    """
    n = PERIOD_DAYS[period]
    base_day = (today - dt.timedelta(days=n)).isoformat()
    snaps = hist.get("snapshots", [])
    dates = [s["date"] for s in snaps]
    status = {"days": len(snaps), "need_day": base_day, "ready": base_day in dates}
    # 按现有记录推算哪天开始生效（假设之后每天都正常运行）：最早的“某次快照 + N 天”且不早于今天
    future = sorted(dt.date.fromisoformat(d) + dt.timedelta(days=n) for d in dates)
    ready_on = next((x for x in future if x >= today), None)
    status["ready_on"] = ready_on.isoformat() if ready_on else None
    if not status["ready"]:
        return [], status
    bi = dates.index(base_day)
    base = snaps[bi]
    base_end = _cn_midnight(dt.date.fromisoformat(base_day) + dt.timedelta(days=1))
    out = []
    for rid, r in found.items():
        entry = hist["repos"].get(rid, {})
        series = entry.get("s", [None] * len(snaps))
        prev = series[bi]
        created = r.get("created_at") and dt.datetime.strptime(r["created_at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
        approx = False
        if prev is not None:
            gain = r["stars"] - prev
        elif created and created >= base_end:
            gain = r["stars"]
        elif entry.get("t", "") > base_day:
            # 后来才通过 README 发现、加入跟踪的项目：t 那天起的记录才可靠（之前没记录不代表不到门槛）。
            # 用 t 那天的星数算，得到的是这段时间里后一部分的涨星，标为下限
            j = next((k for k in range(bi + 1, len(snaps) - 1) if snaps[k]["date"] >= entry["t"]), None)
            if j is None:
                continue
            if series[j] is not None:
                gain = r["stars"] - series[j]
            elif snaps[j].get("complete") and snaps[j].get("min_stars"):
                gain = r["stars"] - (snaps[j]["min_stars"] - 1)
            else:
                continue
            approx = True
        elif base.get("complete") and base.get("min_stars"):
            gain = r["stars"] - (base["min_stars"] - 1)
            approx = True
        else:
            continue
        if gain > 0:
            item = {k: r[k] for k in ("repo", "url", "desc", "language", "lang_color", "stars", "forks")}
            item.update({"period_stars": gain, "approx": approx, "src": ["tracked"]})
            if entry.get("r") == "readme":
                item["readme_zh"] = True
            out.append(item)
    out.sort(key=lambda x: -x["period_stars"])
    return out[:top], status


def merge_lists(trending: list[dict], tracked: list[dict]) -> list[dict]:
    """合并 Trending 和全量跟踪的结果。两边都有时，用跟踪算出的准确涨星（不是下限时），并标两个来源。"""
    merged: dict[str, dict] = {}
    for r in trending:
        r = {k: v for k, v in r.items() if k not in ("is_new", "days")}
        r["src"] = ["trending"]
        r.pop("approx", None)
        merged[r["repo"]] = r
    for t in tracked:
        cur = merged.get(t["repo"])
        if cur is None:
            merged[t["repo"]] = dict(t)
        else:
            cur["src"] = ["trending", "tracked"]
            if not t["approx"]:
                cur["period_stars"] = t["period_stars"]
            cur["stars"] = max(cur["stars"], t["stars"])
    return list(merged.values())


def run_tracking(args, token: str, today: dt.date) -> int:
    """--track 模式：全量扫描 → 更新历史 → 算日/周/月涨星 → 合并进网站数据。"""
    hist_path = Path(args.history)
    hist = json.loads(hist_path.read_text(encoding="utf-8")) if hist_path.exists() and hist_path.stat().st_size else {}
    state_dir = Path(args.state_dir)
    keep = set(hist.get("repos", {}).keys())
    for p in PERIOD_DAYS:
        keep |= {k for k in load_state(state_dir / f"seen_{p}.json") if k != "_meta"}

    stats = {"queries": 0, "failed": [], "incomplete": [], "capped": [], "unfinished": [], "scanned_ids": set(),
             "others": {}}
    all_path = hist_path.parent / ALL_STARS_FILE
    prev_all = load_all_stars(all_path)
    t0 = time.monotonic()
    found = enumerate_repos(args.track_min_stars, token, t0 + args.time_budget * 60, keep, stats)
    complete = not (stats["failed"] or stats["unfinished"] or stats["incomplete"] or stats["capped"])
    seconds = round(time.monotonic() - t0)

    # 简介不是中文、README 是中文的项目：按前一天到今天的涨星挑一批检查 README
    by_readme, rinfo = discover_by_readme(hist, stats["others"], prev_all, today, token, args.readme_check,
                                          t0 + (args.time_budget + 10) * 60)
    found.update(by_readme)
    update_history(hist, today, args.track_min_stars, complete, found)
    snap_dates = [s["date"] for s in hist["snapshots"]]
    yday = (today - dt.timedelta(days=1)).isoformat()
    prev_stars = prev_all.get("stars", {})
    for rid in by_readme:
        entry = hist["repos"][rid]
        entry["r"] = "readme"
        # t：从哪天起这个项目的记录是可靠的。前一天的星数在全部仓库的记录里有，就补进历史（当天的日涨星就是准确的）；
        # 前一天的扫描是完整的而里面没有它，说明当时不到门槛。这两种情况都从前一天算起，否则从今天算起
        entry["t"] = today.isoformat()
        if yday in snap_dates and (rid in prev_stars or prev_all.get("complete")):
            entry["t"] = yday
            if rid in prev_stars:
                entry["s"][snap_dates.index(yday)] = prev_stars[rid]
    hist_path.parent.mkdir(parents=True, exist_ok=True)
    hist_path.write_text(json.dumps(hist, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    save_all_stars(all_path, today, args.track_min_stars, complete, found, stats["others"])
    stats["others"].clear()
    summary = {
        "min_stars": args.track_min_stars, "scanned": len(stats["scanned_ids"]), "tracked": len(found),
        "queries": stats["queries"], "complete": complete, "seconds": seconds,
        "problems": (stats["failed"] + [f"{x}（结果不完整）" for x in stats["incomplete"]]
                     + [f"{x}（超过 1000 条上限）" for x in stats["capped"]])[:20],
        "unfinished": len(stats["unfinished"]),
        "readme": dict(rinfo, total=sum(1 for e in hist["repos"].values() if e.get("r") == "readme")),
    }
    print(f"[info] track：扫描 {summary['scanned']} 个 {args.track_min_stars} 星以上的仓库，中文 {summary['tracked']} 个，"
          f"查询 {summary['queries']} 次，用时 {summary['seconds']} 秒，{'完整' if complete else '不完整'}", file=sys.stderr)
    print(f"[info] README 检查：候选 {rinfo['candidates']} 个，检查 {rinfo['checked']} 个，新发现中文 {rinfo['added']} 个，"
          f"出错 {rinfo['errors']} 个{('，' + rinfo['stopped']) if rinfo['stopped'] else ''}；"
          f"累计靠 README 跟踪 {summary['readme']['total']} 个", file=sys.stderr)

    if not args.site_dir:
        return 0
    site_dir = Path(args.site_dir)
    for p in PERIOD_DAYS:
        f = site_dir / "data" / f"{p}.json"
        if not f.exists():
            continue
        data = json.loads(f.read_text(encoding="utf-8"))
        trending = [r for r in data["repos"] if "trending" in r.get("src", ["trending"])]
        gains, status = tracked_gains(hist, found, today, p, args.track_top)
        merged = merge_lists(trending, gains)
        state_path = state_dir / f"seen_{p}.json"
        state = load_state(state_path)
        meta = state.setdefault("_meta", {})
        if status["ready"]:
            meta.setdefault("tracked_since", today.isoformat())
        first_run = mark_new(merged, state, today, args.cooldown)
        if meta.get("tracked_since") == today.isoformat():
            # 全量跟踪第一次并入这个榜：Trending 以外的项目不标“新”，否则一下子全是新的
            for r in merged:
                if r["src"] == ["tracked"] and r["is_new"]:
                    r["is_new"] = False
                    state[r["repo"]].pop("new_on", None)
        merged.sort(key=lambda r: r["period_stars"], reverse=True)
        data["repos"] = merged
        data["first_run"] = first_run
        data["generated_at"] = dt.datetime.now(dt.timezone.utc).isoformat(timespec="minutes")
        data.setdefault("coverage", {})["tracked"] = dict(summary, **status,
                                                            added=sum(1 for r in merged if r["src"] == ["tracked"]))
        f.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
        state_path.write_text(json.dumps(state, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8")
    add_readme_to_new(site_dir, state_dir, hist, found, today, args.cooldown)
    print(f"[info] 网站已生成：{build_site(site_dir)}", file=sys.stderr)
    return 0


def add_readme_to_new(site_dir: Path, state_dir: Path, hist: dict, found: dict, today: dt.date, cooldown: int) -> int:
    """新项目榜只看简介；把靠 README 认出来的、在统计时间段内新建的中文项目也补进去。返回补了几个。"""
    f = site_dir / "data" / "new.json"
    if not f.exists():
        return 0
    data = json.loads(f.read_text(encoding="utf-8"))
    cov = data.get("coverage", {})
    if not cov.get("start"):
        return 0
    start = _cn_midnight(dt.date.fromisoformat(cov["start"]))
    min_stars = cov.get("min_stars", 100)
    batch = set(cov.get("batch_repos", []))
    have = {r["repo"] for r in data["repos"]}
    now = dt.datetime.now(dt.timezone.utc)
    added = []
    for rid, r in found.items():
        if hist["repos"].get(rid, {}).get("r") != "readme" or r["repo"] in have or not r.get("created_at"):
            continue
        created = dt.datetime.strptime(r["created_at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
        if created < start or r["stars"] < min_stars:
            continue
        age = max(1.0, (now - created).total_seconds() / 86400)
        added.append({k: r[k] for k in ("repo", "url", "desc", "language", "lang_color", "stars", "forks")} | {
            "period_stars": r["stars"], "created": created.astimezone(CN_TZ).strftime("%Y-%m-%d"),
            "age_days": round(age, 1), "per_day": round(r["stars"] / age, 1),
            "batch": r["repo"] in batch, "readme_zh": True})
    if not added:
        return 0
    state_path = state_dir / "seen_new.json"
    state = load_state(state_path)
    mark_new(added, state, today, cooldown)
    data["repos"] += added
    data["repos"].sort(key=lambda r: r["period_stars"], reverse=True)
    cov["readme_added"] = len(added)
    f.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
    state_path.write_text(json.dumps(state, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8")
    return len(added)


# ---------------------------------------------------------------- 新上榜判定

def load_state(path: Path) -> dict:
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {}


def mark_new(repos: list[dict], state: dict, today: dt.date, cooldown: int) -> bool:
    """
    给每个项目打上 is_new 和 days（累计在榜天数），并更新 state。返回是否为首次运行。

    “新上榜”= 从没见过，或者离上次在榜已超过 cooldown 天（重新冲上来也算新闻）。
    首次运行（只有今天建立的基线）不标新：没有基线，“新”没有意义。
    同一天重复运行，结果保持一致。
    """
    t = today.isoformat()
    meta = state.setdefault("_meta", {})
    # 老版本的记录文件没有 _meta：用最早的 first 日期当基线
    meta.setdefault("baseline", min((v["first"] for k, v in state.items() if k != "_meta"), default=t))
    first_run = meta["baseline"] == t
    for r in repos:
        s = state.get(r["repo"])
        if first_run:
            is_new = False
        elif s is None or s.get("new_on") == t:
            is_new = True
        else:
            is_new = (today - dt.date.fromisoformat(s["last"])).days > cooldown
        s = s or {"first": t, "days": 0}
        if s.get("last") != t:
            s["days"] = s.get("days", 0) + 1
        s["last"] = t
        if is_new:
            s["new_on"] = t
        state[r["repo"]] = s
        r["is_new"] = is_new
        r["days"] = s["days"]
    return first_run


# ---------------------------------------------------------------- 输出：Markdown / 推送

def growth(r: dict) -> float:
    """热门榜：本期新增 ÷ 总星；新项目榜：建库以来日均星数。"""
    if "per_day" in r:
        return r["per_day"]
    return r["period_stars"] / max(r["stars"], 1)


def coverage_note(cov: dict) -> str:
    if cov.get("kind") == "search":
        if cov["failed"]:
            return (f"⚠️ 有 {len(cov['failed'])} 个时间段搜索失败（{'; '.join(cov['failed'][:3])}"
                    f"{' 等' if len(cov['failed']) > 3 else ''}），新项目榜可能不完整。")
        rd = cov.get("readme") or {}
        how = f"简介或 README 为中文的 {cov['chinese']} 个（其中看 README 认出的 {rd['zh']} 个）" if rd \
            else f"简介含中文的 {cov['chinese']} 个"
        tail = f"还有 {rd['pending']} 个简介不是中文的没来得及看 README，下次继续。" if rd.get("pending") else ""
        return (f"已搜索北京时间 {cov.get('start', '')} 起的全部时间段：{cov['candidates']} 个新建且 {cov['min_stars']} 星以上的仓库，"
                f"{how}（其中疑似批量刷星 {cov['batch']} 个）。{tail}")
    if not cov.get("full_sweep"):
        return f"⚠️ 只抓了指定的 {cov['pages'] - 1} 个语言分榜，榜单不完整。"
    if cov["failed"]:
        return (f"⚠️ 有 {len(cov['failed'])} 个分榜重试后仍抓取失败（{', '.join(cov['failed'][:8])}"
                f"{' 等' if len(cov['failed']) > 8 else ''}），榜单可能不完整。")
    return f"已抓取全部 {cov['pages']} 个分榜（总榜 + 全部语言），无遗漏。"


def render_markdown(repos: list[dict], since: str, today: dt.date, title: str, first_run: bool,
                    cov: dict, total: int, site_url: str = "") -> str:
    label = PERIOD_LABEL[since]
    lines = [f"# {title} · {today.isoformat()}（{label}）", ""]
    if since == "new":
        head = (f"近 {cov.get('days', 30)} 天（北京时间 {cov.get('start', '')} 起）新建的中文项目共 {total} 个"
                f"（已去掉疑似批量刷星的）")
    else:
        head = f"{label}共 {total} 个中文热门项目"
    if first_run:
        head += "。首次运行，已把这期榜单记为基线，下次起标出新上榜项目。"
    else:
        head += f"，其中 🆕 新上榜 {sum(r['is_new'] for r in repos)} 个。"
    if len(repos) < total:
        head += f"下面列出 {len(repos)} 个。"
    lines += [head, "", coverage_note(cov), ""]
    if site_url:
        lines += [f"完整榜单：{site_url}", ""]

    def block(items: list[dict]) -> None:
        for i, r in enumerate(items, 1):
            tag = " 🆕" if r["is_new"] else ""
            lang = f" · {r['language']}" if r["language"] else ""
            if "per_day" in r:
                stat = f"⭐ {r['stars']:,} · 建库 {r['age_days']:.0f} 天 · 日均 {r['per_day']:,.1f}"
            else:
                stat = f"⭐ +{r['period_stars']:,} / {r['stars']:,}（{growth(r):.1%}）"
            lines.append(f"{i}. **[{r['repo']}]({r['url']})**{tag}{lang} · {stat}")
            if r["desc"]:
                lines.append(f"   {r['desc']}")
        lines.append("")

    new_items = [r for r in repos if r["is_new"]]
    old_items = [r for r in repos if not r["is_new"]]
    if new_items:
        lines += ["## 🆕 新上榜", ""]
        block(new_items)
    if old_items:
        lines += ["## 持续在榜" if new_items else "## 榜单", ""]
        block(old_items)
    if not repos:
        lines.append("没有符合条件的项目。")
    return "\n".join(lines).rstrip() + "\n"


def _trim_bytes(text: str, limit: int) -> str:
    """按字节截断（中文 3 字节/字），在行边界截，避免把链接截一半。"""
    if len(text.encode("utf-8")) <= limit:
        return text
    out, size = [], 0
    tail = "\n…（内容过长已截断）"
    budget = limit - len(tail.encode("utf-8"))
    for line in text.splitlines(keepends=True):
        b = len(line.encode("utf-8"))
        if size + b > budget:
            break
        out.append(line)
        size += b
    return "".join(out) + tail


def push_webhook(url: str, kind: str, title: str, md: str) -> None:
    """
    推送到群机器人。建议在机器人安全设置里用“自定义关键词”，填 GitHub（消息标题里带这个词）。
    """
    if kind == "feishu":
        payload = {"msg_type": "interactive", "card": {
            "header": {"title": {"tag": "plain_text", "content": title}},
            "elements": [{"tag": "markdown", "content": _trim_bytes(md, 20000)}]}}
    elif kind == "dingtalk":
        payload = {"msgtype": "markdown", "markdown": {"title": title, "text": _trim_bytes(md, 15000)}}
    elif kind == "wecom":
        # 企业微信 markdown 消息上限 4096 字节
        payload = {"msgtype": "markdown", "markdown": {"content": _trim_bytes(md, 4000)}}
    else:
        raise ValueError(f"不支持的 webhook 类型：{kind}")
    r = requests.post(url, json=payload, timeout=20)
    r.raise_for_status()
    print(f"[info] 已推送到 {kind}：{r.text[:200]}", file=sys.stderr)


# ---------------------------------------------------------------- 输出：网站

def write_site_data(site_dir: Path, since: str, today: dt.date, repos: list[dict], first_run: bool,
                    coverage: dict | None = None) -> None:
    data_dir = site_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "since": since,
        "date": today.isoformat(),
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="minutes"),
        "first_run": first_run,
        "coverage": coverage or {},
        "repos": repos,
    }
    (data_dir / f"{since}.json").write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")


def build_site(site_dir: Path, template_path: Path = TEMPLATE_PATH) -> Path:
    """把 site_dir/data/ 里已有的日榜、周榜、月榜数据嵌进模板，生成 site_dir/index.html。"""
    periods = {}
    for since in PERIOD_LABEL:
        f = site_dir / "data" / f"{since}.json"
        if f.exists():
            periods[since] = json.loads(f.read_text(encoding="utf-8"))
    if not periods:
        raise RuntimeError(f"{site_dir / 'data'} 里还没有数据")
    data = {"generated_at": max(p["generated_at"] for p in periods.values()), "periods": periods}
    blob = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")  # 防止描述里的 </script> 提前结束脚本
    template = template_path.read_text(encoding="utf-8")
    if DATA_PLACEHOLDER not in template:
        raise RuntimeError(f"模板里找不到占位符 {DATA_PLACEHOLDER}")
    out = site_dir / "index.html"
    out.write_text(template.replace(DATA_PLACEHOLDER, blob, 1), encoding="utf-8")
    return out


# ---------------------------------------------------------------- 主流程

def main() -> int:
    p = argparse.ArgumentParser(description="GitHub 中文热门（spoken_language=zh）日榜 / 周榜 / 月榜")
    p.add_argument("--since", choices=list(PERIOD_LABEL), default="daily")
    p.add_argument("--lang", action="append", default=[],
                   help="只抓指定的语言分榜（可重复）。不填 = 总榜 + 全部语言分榜（推荐，无遗漏）")
    p.add_argument("--workers", type=int, default=4, help="并发抓取线程数（默认 4）")
    p.add_argument("--interval", type=float, default=0.25, help="两次请求之间的最小间隔秒数（默认 0.25）")
    p.add_argument("--sort", choices=["period", "growth"], default="period",
                   help="period=按本期新增 star（默认）；growth=按新增/总 star 的比例")
    p.add_argument("--min-stars", type=int, default=0, help="本期新增 star 少于该值的不要")
    p.add_argument("--only-new", action="store_true",
                   help="存档和推送只包含新上榜的项目（网站仍显示完整榜单；首次运行时不生效）")
    p.add_argument("--cooldown", type=int, default=7,
                   help="离上次在榜超过多少天再上榜，算作新上榜（默认 7）")
    p.add_argument("--exclude", action="append", default=[], help="排除的仓库 owner/name，可重复")
    p.add_argument("--state-dir", default="data", help="存放见过项目记录和 Markdown 存档的目录")
    p.add_argument("--site-dir", default="", help="生成静态网站的目录，如 docs（配合 GitHub Pages）")
    p.add_argument("--site-url", default=os.environ.get("SITE_URL", ""), help="网站地址，会附在推送消息里")
    p.add_argument("--title", default="GitHub 中文热门")
    p.add_argument("--push-top", type=int, default=30, help="推送消息最多列出多少个项目（默认 30，完整榜单看网站）")
    p.add_argument("--webhook", default=os.environ.get("TRENDING_WEBHOOK", ""),
                   help="群机器人 webhook 地址（也可用环境变量 TRENDING_WEBHOOK）")
    p.add_argument("--webhook-type", choices=["feishu", "dingtalk", "wecom"],
                   default=os.environ.get("TRENDING_WEBHOOK_TYPE", "feishu"))
    p.add_argument("--no-push", action="store_true", help="这次不推送")
    p.add_argument("--dry-run", action="store_true", help="不写入任何文件、不推送，只打印结果")
    p.add_argument("--new-days", type=int, default=30, help="新项目榜：统计最近多少天新建的仓库（默认 30）")
    p.add_argument("--new-min-stars", type=int, default=100, help="新项目榜：至少多少星（默认 100）")
    p.add_argument("--new-readme-minutes", type=int, default=20,
                   help="新项目榜：最多花多少分钟看简介不是中文的候选的 README（默认 20，没看完的下次继续）")
    p.add_argument("--keep-batch", action="store_true",
                   help="新项目榜：存档和推送里保留疑似批量刷星的仓库（默认去掉；网站上可以手动显示）")
    p.add_argument("--track", action="store_true",
                   help="全量星数跟踪：扫描全 GitHub 达到门槛的仓库，算日/周/月涨星并合并进网站的日榜、周榜、月榜")
    p.add_argument("--track-min-stars", type=int, default=100, help="全量跟踪的星数门槛（默认 100）")
    p.add_argument("--history", default="history/history.json", help="全量跟踪的历史星数文件")
    p.add_argument("--track-top", type=int, default=200, help="每个榜单最多并入多少个跟踪发现的项目（默认 200）")
    p.add_argument("--readme-check", type=int, default=300,
                   help="全量跟踪：每天最多检查多少个简介不是中文的仓库的 README（按前一天涨星挑，默认 300）")
    p.add_argument("--time-budget", type=int, default=320,
                   help="全量扫描最多用多少分钟（默认 320，GitHub 单个任务上限 360 分钟），超时就停下并如实标注")
    args = p.parse_args()

    global _pacer, _search_pacer
    _pacer = Pacer(args.interval)
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        _search_pacer = Pacer(6.5)   # 没有 token 时搜索接口每分钟只允许 10 次
    today = today_cn()
    if args.track:
        return run_tracking(args, token, today)
    state_dir = Path(args.state_dir)
    state_path = state_dir / f"seen_{args.since}.json"

    t0 = time.monotonic()
    readme_path = state_dir / "readme_new.json"
    if args.since == "new":
        readme_cache = load_state(readme_path)
        repos, cov = collect_new(args.new_days, args.new_min_stars, token, readme_cache=readme_cache,
                                 deadline=time.monotonic() + args.new_readme_minutes * 60)
    else:
        repos, cov = collect(args.since, args.lang, args.workers)
    cov["seconds"] = round(time.monotonic() - t0)
    print(f"[info] {args.since}：{coverage_note(cov)} 共 {len(repos)} 个项目，用时 {cov['seconds']} 秒", file=sys.stderr)

    excluded = {x.strip("/").lower() for x in args.exclude}
    repos = [r for r in repos if r["repo"].lower() not in excluded and r["period_stars"] >= args.min_stars]

    state = load_state(state_path)
    first_run = mark_new(repos, state, today, args.cooldown)

    key = growth if args.sort == "growth" else (lambda r: r["period_stars"])
    repos.sort(key=key, reverse=True)
    shown = repos if args.keep_batch else [r for r in repos if not r.get("batch")]
    report = [r for r in shown if r["is_new"]] if (args.only_new and not first_run) else shown

    md_full = render_markdown(report, args.since, today, args.title, first_run, cov, len(shown), args.site_url)
    print(md_full)

    if args.dry_run:
        return 0

    state_dir.mkdir(parents=True, exist_ok=True)
    state_path.write_text(json.dumps(state, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8")
    if args.since == "new":
        # 一行一个仓库，每天的改动在 git 里只占几行
        readme_path.write_text("{\n" + ",\n".join(f"{json.dumps(k)}:{json.dumps(v, sort_keys=True)}"
                                                   for k, v in sorted(readme_cache.items())) + "\n}\n", encoding="utf-8")
    archive = state_dir / "archive" / f"{today.isoformat()}-{args.since}.md"
    archive.parent.mkdir(parents=True, exist_ok=True)
    archive.write_text(md_full, encoding="utf-8")

    if args.site_dir:
        site_dir = Path(args.site_dir)
        write_site_data(site_dir, args.since, today, repos, first_run, cov)
        print(f"[info] 网站已生成：{build_site(site_dir)}", file=sys.stderr)

    if args.webhook and report and not args.no_push:
        md_push = render_markdown(report[:args.push_top], args.since, today, args.title, first_run,
                                  cov, len(shown), args.site_url)
        push_webhook(args.webhook, args.webhook_type, f"{args.title}（{PERIOD_LABEL[args.since]}）", md_push)
    return 0


if __name__ == "__main__":
    sys.exit(main())
