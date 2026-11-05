#!/usr/bin/env python3
"""
Remote DevOps/SRE job digest.

What it does (no logins, no auto-applying):
  1. Pulls public remote-job feeds (Remotive, Remote OK, We Work Remotely, Himalayas)
  2. Keeps only DevOps/SRE/Cloud roles that are open to candidates in India
  3. Removes suspected fake/scam postings, stale posts and dead links
  4. Scores each job against your skills (GCP, GKE, Terraform, Istio, ...)
  5. Emails you ONE consolidated table with a one-click Apply link per job
  6. Remembers what it already sent, so you never get the same job twice

Usage:
  python job_digest.py --dry-run          # builds digest.html, sends nothing
  python job_digest.py --dry-run --ignore-seen
  python job_digest.py                    # sends the email

Required env vars for sending (Gmail example):
  SMTP_USER          your Gmail address
  SMTP_APP_PASSWORD  a Gmail *App Password* (not your normal password)
  EMAIL_TO           where to send the digest (defaults to SMTP_USER)
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import smtplib
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from pathlib import Path

import requests

# --------------------------------------------------------------------------
# CONFIG - edit these to tune the digest
# --------------------------------------------------------------------------
MAX_AGE_DAYS = 14               # ignore postings older than this
MAX_REQUIRED_YEARS = 8         # skip jobs that ask for more than this many years
MIN_SCORE = 5                  # minimum skill-match score to be listed
ALLOW_UNCLEAR_LOCATION = False # True = also list jobs whose location can't be determined
MAX_JOBS_IN_EMAIL = 40
SEND_EMAIL_WHEN_EMPTY = True   # send a short "nothing new today" mail so you know it ran
SEEN_FILE = os.environ.get("SEEN_FILE", "seen_jobs.json")
SEEN_KEEP_DAYS = 60

# Companies you never want to see (lowercase)
COMPANY_BLOCKLIST: set[str] = set()

# Job titles we want / don't want
TITLE_INCLUDE = re.compile(
    r"devops|dev-ops|\bsre\b|site reliability|platform engineer|cloud engineer|"
    r"cloud infrastructure|infrastructure engineer|kubernetes|\bgcp\b|devsecops|"
    r"cloud ops|production engineer",
    re.I,
)
TITLE_EXCLUDE = re.compile(
    r"\b(intern|internship|trainee|fresher|junior|jr\.?|associate|entry[- ]level|"
    r"director|vp|vice president|head of|manager)\b",
    re.I,
)

# Your skills: name -> (regex, weight)
SKILLS: dict[str, tuple[str, int]] = {
    "GCP": (r"\b(gcp|google cloud)\b", 3),
    "GKE": (r"\bgke\b", 3),
    "Kubernetes": (r"\b(kubernetes|k8s)\b", 3),
    "Terraform": (r"\bterraform\b", 3),
    "Istio": (r"\b(istio|service mesh|anthos)\b", 2),
    "Helm": (r"\bhelm\b", 2),
    "Jenkins": (r"\bjenkins\b", 2),
    "ArgoCD/GitOps": (r"\b(argo ?cd|gitops)\b", 2),
    "SRE": (r"\b(sre|site reliability)\b", 2),
    "Prometheus": (r"\bprometheus\b", 1),
    "Grafana": (r"\bgrafana\b", 1),
    "Docker": (r"\bdocker\b", 1),
    "Observability": (r"\b(observability|opentelemetry|dynatrace|datadog)\b", 1),
    "GitHub Actions": (r"github actions", 1),
}

# --------------------------------------------------------------------------
# Fake / scam detection
# --------------------------------------------------------------------------
HARD_SCAM = [re.compile(p, re.I) for p in (
    r"registration fee", r"security deposit", r"processing fee", r"training fee",
    r"refundable (deposit|fee|amount)", r"pay (a |an )?(small )?(fee|deposit|amount)",
    r"(contact|message|send|apply|reach).{0,40}(whatsapp|telegram)",
    r"(whatsapp|telegram).{0,20}(number|id|no\.)", r"wa\.me/", r"t\.me/",
    r"(send|share|provide).{0,30}(bank|aadhaar|aadhar|pan card)",
    r"earn\s*[\$₹]?\s*\d[\d,]*\s*(per|a|/)\s*(day|hour|week)",
    r"no experience (is )?(needed|required|necessary)",
    r"guaranteed (income|job|placement|salary)", r"data entry", r"typing job",
    r"\bmlm\b|multi-level marketing", r"investment (is )?required", r"western union",
    r"(check|cheque) (will be )?(sent|mailed)",
)]
SOFT_SCAM = {
    "free-mail contact": re.compile(
        r"[\w.+-]+@(gmail|yahoo|outlook|hotmail|rediffmail|proton(mail)?)\.(com|me|in)", re.I),
    "urgent-hiring language": re.compile(
        r"urgent(ly)? hiring|immediate joiners?|walk-?in|hiring now!", re.I),
    "link shortener": re.compile(r"bit\.ly|tinyurl|cutt\.ly|goo\.gl|rb\.gy|is\.gd", re.I),
    "gift cards": re.compile(r"gift cards?", re.I),
}
GENERIC_COMPANIES = {"", "confidential", "hiring", "company", "n/a", "undisclosed", "anonymous"}

# --------------------------------------------------------------------------
# Location eligibility (India)
# --------------------------------------------------------------------------
INDIA_CITIES = r"india|bangalore|bengaluru|hyderabad|pune|chennai|mumbai|delhi|gurgaon|gurugram|noida|kolkata|ahmedabad"
OK_PAT = re.compile(r"\b(worldwide|world[- ]wide|anywhere|global|globally|apac|asia|any location)\b", re.I)
BLOCK_PAT = re.compile(
    r"\b(us|usa|u\.s\.a?\.?|united states|canada|uk|united kingdom|europe|eu|emea|latam|"
    r"latin america|americas|north america|australia|new zealand|brazil|mexico|germany|"
    r"france|spain|poland|netherlands|ireland|israel|uae|south africa|nigeria)\b", re.I)
DESC_BLOCK = re.compile(
    r"(must|should|need to) (be located|reside|be based|live) in (the )?(us|usa|united states|uk|europe|eu|canada)|"
    r"(us|u\.s\.) (citizens?|work authori[sz]ation)|"
    r"(authori[sz]ed|eligible|right) to work in (the )?(us|u\.s\.|united states|uk|eu|canada)", re.I)


def location_status(location: str, description: str = "") -> str:
    t = (location or "").lower()
    t_clean = re.sub(r"anywhere in (the )?(us|usa|u\.s\.a?\.?|united states|uk|europe|eu|canada|americas)", " ", t)
    regional_only = t_clean != t
    t = t_clean
    if re.search(r"(excluding|except|not open to|excl\.?) (india|asia)", t):
        return "blocked"
    if regional_only and not re.search(rf"\b({INDIA_CITIES})\b", t) and not OK_PAT.search(t):
        return "blocked"
    if re.search(rf"\b({INDIA_CITIES})\b", t):
        return "ok"
    if DESC_BLOCK.search(description or ""):
        return "blocked"
    if OK_PAT.search(t):
        return "ok"
    if not t.strip():
        return "unclear"
    if BLOCK_PAT.search(t):
        return "blocked"
    return "unclear"


# --------------------------------------------------------------------------
# Data model + helpers
# --------------------------------------------------------------------------
@dataclass
class Job:
    source: str
    title: str
    company: str
    location: str
    url: str
    posted: datetime | None = None
    salary: str = ""
    description: str = ""
    score: int = 0
    matched: list = field(default_factory=list)


def strip_html(s: str) -> str:
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def parse_date(v) -> datetime | None:
    if v in (None, ""):
        return None
    try:
        if isinstance(v, (int, float)) or (isinstance(v, str) and v.strip().isdigit()):
            n = float(v)
            if n > 1e12:
                n /= 1000
            return datetime.fromtimestamp(n, tz=timezone.utc)
        v = str(v).strip()
        try:
            d = datetime.fromisoformat(v.replace("Z", "+00:00"))
        except ValueError:
            d = parsedate_to_datetime(v)
        if d.tzinfo is None:
            d = d.replace(tzinfo=timezone.utc)
        return d.astimezone(timezone.utc)
    except Exception:
        return None


def fmt_salary(lo, hi, cur="USD") -> str:
    try:
        lo, hi = int(lo or 0), int(hi or 0)
    except (TypeError, ValueError):
        return ""
    if lo and hi:
        return f"{cur} {lo:,}-{hi:,}"
    if lo or hi:
        return f"{cur} {max(lo, hi):,}"
    return ""


def job_key(j: Job) -> str:
    norm = lambda x: re.sub(r"[^a-z0-9]+", " ", (x or "").lower()).strip()
    return hashlib.sha1(f"{norm(j.company)}|{norm(j.title)}".encode()).hexdigest()[:16]


def safe_url(u: str) -> bool:
    return isinstance(u, str) and u.startswith(("https://", "http://"))


def http_get(session: requests.Session, url: str, **kw) -> requests.Response:
    last = None
    for attempt in range(3):
        try:
            r = session.get(url, timeout=25, **kw)
            r.raise_for_status()
            return r
        except requests.RequestException as e:
            last = e
            time.sleep(1.5 * (attempt + 1))
    raise last  # type: ignore[misc]


# --------------------------------------------------------------------------
# Sources (public feeds, no login)
# --------------------------------------------------------------------------
def fetch_remotive(s: requests.Session) -> list[Job]:
    jobs = []
    for params in ({"category": "devops", "limit": 150}, {"search": "kubernetes", "limit": 100}):
        data = http_get(s, "https://remotive.com/api/remote-jobs", params=params).json()
        for it in data.get("jobs", []):
            jobs.append(Job(
                source="Remotive", title=it.get("title", ""), company=it.get("company_name", ""),
                location=it.get("candidate_required_location", ""), url=it.get("url", ""),
                posted=parse_date(it.get("publication_date")), salary=it.get("salary", "") or "",
                description=strip_html(it.get("description", "")),
            ))
    return jobs


def fetch_remoteok(s: requests.Session) -> list[Job]:
    data = http_get(s, "https://remoteok.com/api").json()
    jobs = []
    for it in data:
        if not isinstance(it, dict) or "position" not in it:
            continue
        jobs.append(Job(
            source="Remote OK", title=it.get("position", ""), company=it.get("company", ""),
            location=it.get("location", "") or "Worldwide",
            url=it.get("url", ""), posted=parse_date(it.get("date") or it.get("epoch")),
            salary=fmt_salary(it.get("salary_min"), it.get("salary_max")),
            description=strip_html(it.get("description", "")) + " " + " ".join(it.get("tags", []) or []),
        ))
    return jobs


def fetch_wwr(s: requests.Session) -> list[Job]:
    r = http_get(s, "https://weworkremotely.com/categories/remote-devops-sysadmin-jobs.rss")
    root = ET.fromstring(r.content)
    jobs = []
    for item in root.iter("item"):
        raw_title = (item.findtext("title") or "").strip()
        company, sep, title = raw_title.partition(": ")
        if not sep:
            company, title = "", raw_title
        jobs.append(Job(
            source="We Work Remotely", title=title, company=company,
            location=(item.findtext("region") or "").strip(),
            url=(item.findtext("link") or "").strip(),
            posted=parse_date(item.findtext("pubDate")),
            description=strip_html(item.findtext("description") or ""),
        ))
    return jobs


def fetch_himalayas(s: requests.Session) -> list[Job]:
    jobs = []
    for offset in range(0, 100, 20):
        data = http_get(s, "https://himalayas.app/jobs/api", params={"limit": 20, "offset": offset}).json()
        batch = data.get("jobs", [])
        if not batch:
            break
        for it in batch:
            locs = it.get("locationRestrictions") or []
            jobs.append(Job(
                source="Himalayas", title=it.get("title", ""), company=it.get("companyName", ""),
                location=", ".join(locs) if locs else "Worldwide (no restriction listed)",
                url=it.get("applicationLink") or it.get("guid", ""),
                posted=parse_date(it.get("pubDate")),
                salary=fmt_salary(it.get("minSalary"), it.get("maxSalary"), it.get("currency") or "USD"),
                description=strip_html(it.get("description", "") or it.get("excerpt", "")),
            ))
    return jobs


SOURCES = [
    ("Remotive", fetch_remotive),
    ("Remote OK", fetch_remoteok),
    ("We Work Remotely", fetch_wwr),
    ("Himalayas", fetch_himalayas),
]


# --------------------------------------------------------------------------
# Filtering + scoring
# --------------------------------------------------------------------------
def scam_flags(j: Job) -> list[str]:
    text = f"{j.title}\n{j.description}"
    hard = [p.pattern for p in HARD_SCAM if p.search(text)]
    if hard:
        return ["scam phrase"]
    soft = [name for name, p in SOFT_SCAM.items() if p.search(text)]
    if len(j.description) < 250:
        soft.append("very short description")
    if (j.company or "").strip().lower() in GENERIC_COMPANIES:
        soft.append("no real company name")
    if "!" in j.title or (len(j.title) > 8 and j.title.isupper()):
        soft.append("spammy title")
    return soft if len(soft) >= 2 else []


def min_years_required(text: str) -> int | None:
    found = []
    for m in re.finditer(r"(\d{1,2})\s*\+?\s*(?:-|–|to)?\s*(?:\d{1,2})?\s*\+?\s*(?:years|yrs)", text, re.I):
        ctx = text[max(0, m.start() - 80): m.end() + 80].lower()
        if "experience" in ctx:
            found.append(int(m.group(1)))
    return min(found) if found else None


def skill_score(text: str) -> tuple[int, list[str]]:
    total, hits = 0, []
    for name, (pat, w) in SKILLS.items():
        if re.search(pat, text, re.I):
            total += w
            hits.append(name)
    return total, hits


def evaluate(j: Job, now: datetime) -> str | None:
    """Return None if the job is good, otherwise the reason it was dropped."""
    if not safe_url(j.url):
        return "invalid link"
    if (j.company or "").strip().lower() in COMPANY_BLOCKLIST:
        return "blocked company"
    if not TITLE_INCLUDE.search(j.title) or TITLE_EXCLUDE.search(j.title):
        return "not a matching title"
    if j.posted and (now - j.posted) > timedelta(days=MAX_AGE_DAYS):
        return "too old"
    loc = location_status(j.location, j.description)
    if loc == "blocked":
        return "not open to India"
    if loc == "unclear" and not ALLOW_UNCLEAR_LOCATION:
        return "location unclear"
    if scam_flags(j):
        return "suspected fake/scam"
    text = f"{j.title}\n{j.description}"
    yrs = min_years_required(text)
    if yrs is not None and yrs > MAX_REQUIRED_YEARS:
        return "asks for too many years"
    j.score, j.matched = skill_score(text)
    if j.score < MIN_SCORE:
        return "low skill match"
    return None


def link_alive(s: requests.Session, url: str) -> bool:
    try:
        r = s.get(url, timeout=12, stream=True, allow_redirects=True)
        r.close()
        return r.status_code not in (404, 410)
    except requests.RequestException:
        return True  # can't tell, keep it


# --------------------------------------------------------------------------
# Seen-jobs store
# --------------------------------------------------------------------------
def load_seen() -> dict:
    try:
        return json.loads(Path(SEEN_FILE).read_text())
    except Exception:
        return {}


def save_seen(seen: dict, now: datetime) -> None:
    cutoff = (now - timedelta(days=SEEN_KEEP_DAYS)).date().isoformat()
    pruned = {k: v for k, v in seen.items() if v >= cutoff}
    Path(SEEN_FILE).write_text(json.dumps(pruned, indent=0, sort_keys=True))


# --------------------------------------------------------------------------
# Email
# --------------------------------------------------------------------------
def posted_label(d: datetime | None, now: datetime) -> str:
    if not d:
        return "n/a"
    days = (now - d).days
    return "Today" if days <= 0 else f"{days}d ago"


def build_html(jobs: list[Job], stats: Counter, status: dict, now: datetime) -> str:
    e = html.escape
    th = "padding:8px;border:1px solid #ddd;background:#f3f4f6;text-align:left;font-size:13px"
    td = "padding:8px;border:1px solid #ddd;font-size:13px;vertical-align:top"
    head = "".join(f"<th style='{th}'>{h}</th>" for h in
                   ("#", "Role", "Company", "Location", "Posted", "Match", "Salary", "Source", "Apply"))
    rows = []
    for i, j in enumerate(jobs, 1):
        btn = (f"<a href='{e(j.url, quote=True)}' style='background:#2563eb;color:#fff;padding:6px 12px;"
               f"border-radius:4px;text-decoration:none;font-size:13px'>Apply</a>")
        rows.append(
            "<tr>"
            f"<td style='{td}'>{i}</td><td style='{td}'><b>{e(j.title)}</b></td>"
            f"<td style='{td}'>{e(j.company or '-')}</td><td style='{td}'>{e(j.location or '-')}</td>"
            f"<td style='{td}'>{e(posted_label(j.posted, now))}</td>"
            f"<td style='{td}'><b>{j.score}</b><br><span style='color:#555'>{e(', '.join(j.matched[:6]))}</span></td>"
            f"<td style='{td}'>{e(j.salary or '-')}</td><td style='{td}'>{e(j.source)}</td>"
            f"<td style='{td}'>{btn}</td></tr>")
    jobs_table = (f"<table style='border-collapse:collapse;width:100%'><tr>{head}</tr>{''.join(rows)}</table>"
                  if rows else "<p>No new matching jobs today.</p>")
    stat_rows = "".join(f"<tr><td style='{td}'>{e(k)}</td><td style='{td}'>{v}</td></tr>"
                        for k, v in stats.most_common())
    src_rows = "".join(f"<tr><td style='{td}'>{e(k)}</td><td style='{td}'>{e(v)}</td></tr>"
                       for k, v in status.items())
    return f"""<div style="font-family:Arial,sans-serif;max-width:1000px">
<h2>Remote DevOps/SRE jobs: {len(jobs)} new ({now.strftime('%d %b %Y')})</h2>
<p>Open to India, scam-filtered, sorted by match to your skills. Always verify a company before sharing personal documents.</p>
{jobs_table}
<h3>What was filtered out</h3>
<table style="border-collapse:collapse"><tr><th style='{th}'>Reason</th><th style='{th}'>Count</th></tr>{stat_rows}</table>
<h3>Source status</h3>
<table style="border-collapse:collapse"><tr><th style='{th}'>Source</th><th style='{th}'>Result</th></tr>{src_rows}</table>
<p style="color:#777;font-size:12px">Jobs via Remotive, Remote OK, We Work Remotely and Himalayas. Please apply through the links above.</p>
</div>"""


def build_text(jobs: list[Job], now: datetime) -> str:
    lines = [f"Remote DevOps/SRE jobs: {len(jobs)} new ({now.strftime('%d %b %Y')})", ""]
    for i, j in enumerate(jobs, 1):
        lines.append(f"{i}. {j.title} | {j.company} | {j.location} | match {j.score}\n   {j.url}")
    return "\n".join(lines)


def send_email(subject: str, text: str, html_body: str) -> None:
    user = os.environ.get("SMTP_USER")
    pwd = os.environ.get("SMTP_APP_PASSWORD")
    to = os.environ.get("EMAIL_TO") or user
    if not (user and pwd and to):
        sys.exit("Set SMTP_USER, SMTP_APP_PASSWORD (and optionally EMAIL_TO) to send email.")
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, user, to
    msg.set_content(text)
    msg.add_alternative(html_body, subtype="html")
    with smtplib.SMTP_SSL(os.environ.get("SMTP_HOST", "smtp.gmail.com"), 465, timeout=30) as smtp:
        smtp.login(user, pwd)
        smtp.send_message(msg)


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="write digest.html, do not send or save state")
    ap.add_argument("--ignore-seen", action="store_true", help="include jobs already sent before")
    ap.add_argument("--out", default="digest.html")
    args = ap.parse_args()

    now = datetime.now(timezone.utc)
    ist = now.astimezone(timezone(timedelta(hours=5, minutes=30)))
    s = requests.Session()
    s.headers["User-Agent"] = "remote-job-digest/1.0 (personal job search)"

    all_jobs: list[Job] = []
    status: dict[str, str] = {}
    for name, fn in SOURCES:
        try:
            got = fn(s)
            all_jobs += got
            status[name] = f"{len(got)} fetched"
        except Exception as ex:  # one broken source must not stop the digest
            status[name] = f"FAILED ({type(ex).__name__})"

    seen = {} if args.ignore_seen else load_seen()
    stats: Counter = Counter()
    picked: list[Job] = []
    keys_this_run: set[str] = set()

    for j in all_jobs:
        reason = evaluate(j, now)
        if reason:
            stats[reason] += 1
            continue
        k = job_key(j)
        if k in seen or k in keys_this_run:
            stats["duplicate / already sent"] += 1
            continue
        keys_this_run.add(k)
        picked.append(j)

    picked.sort(key=lambda j: (j.score, j.posted or datetime.min.replace(tzinfo=timezone.utc)), reverse=True)
    picked = picked[:MAX_JOBS_IN_EMAIL + 20]

    final: list[Job] = []
    for j in picked:
        if link_alive(s, j.url):
            final.append(j)
        else:
            stats["dead link"] += 1
    final = final[:MAX_JOBS_IN_EMAIL]

    html_body = build_html(final, stats, status, ist)
    text_body = build_text(final, ist)
    subject = f"Remote DevOps/SRE jobs: {len(final)} new ({ist.strftime('%d %b')})"

    print(f"Sources: {status}")
    print(f"Filtered out: {dict(stats)}")
    print(f"New jobs: {len(final)}")

    if args.dry_run:
        Path(args.out).write_text(html_body, encoding="utf-8")
        print(f"Dry run: wrote {args.out}")
        return

    if final or SEND_EMAIL_WHEN_EMPTY:
        send_email(subject, text_body, html_body)
        print("Email sent.")
    for j in final:
        seen[job_key(j)] = now.date().isoformat()
    save_seen(seen, now)


if __name__ == "__main__":
    main()
