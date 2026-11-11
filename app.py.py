"""약체크 | 일반의약품 구매 전 확인 보조 — Streamlit 단일 화면 앱

실행 / 배포
-----------
1. 이 파일과 requirements.txt를 GitHub 저장소에 올립니다. Python 3.11/3.12 권장.
2. Streamlit Community Cloud에서 저장소를 선택하고 main file을 app.py로 지정.
3. Advanced settings > Secrets에 아래 필요한 값만 설정합니다.
   MFDS_SERVICE_KEY = "공공데이터포털 일반 인증키(Decoding)"
   GOOGLE_VISION_API_KEY = "선택: Cloud Vision API 키"
   # 실제 복약정보를 입력하려면 최소 1개 계정을 설정하세요.
   # password_hash 생성: python app.py --hash-password (비밀번호는 화면에 표시 안 됨)
   [accounts.owner]
   password_hash = "pbkdf2_sha256$310000$...$..."
   role = "owner"  # owner: 가족 추가/삭제+편집, editor: 복약 편집, viewer: 읽기만
   # [accounts.guest]
   # password_hash = "..."
   # role = "viewer"
4. 로컬 실행: pip install -r requirements.txt && streamlit run app.py
5. 로직 검사: python app.py --self-test (공식 데이터 정확도 검증과는 다름)

API 활용신청: 아래 두 서비스를 각각 신청합니다.
- 제품 허가정보 https://www.data.go.kr/data/15095677/openapi.do
- DUR품목정보 https://www.data.go.kr/data/15059486/openapi.do
공식 문서에서 확인한 Service08/Service03 경로 사용. 인증키를 갖고 있지 않은
개발 환경에서는 실 API 응답·배포·카메라를 검증하지 않았습니다. 운영 전 승인된
키로 스키마, 제형/함량, 양방향 병용금기, 바코드/제품코드 매핑을 검증하세요.

개인정보 / 보안
--------------
계정별 브라우저 세션 메모리에만 저장. 다른 세션/가족 계정과 자동 공유 안 됨.
서버 재시작/세션 종료 시 목록 소실 가능. 비밀번호 암호화 백업을 내려받을 수 있음.
가입·공유 DB·의료기관용 감사기록·MFA·계정 잠금은 구현하지 않은 시제품입니다.
공용 인터넷 운영 전 별도 인증 게이트웨이/속도제한/보안 검토를 권장합니다.
공식 API에는 검색어/품목코드만 전달. 사진은 동의 시 Google Vision에 전달.
LLM 사용 없음. 약물 기전은 DUR 공식 원문에 실제 있는 문장만 발췌.
바코드 숫자 자체로 성분을 추정하지 않으며, 공식 결과와 코드가 일치해야 함.
성분은 공식 원문을 보고 사용자가 확인한 명칭으로 정확일치 비교. 염/수화물,
동의어/대사체를 임의 통합하지 않음. 용량합산·일일상한·임부/연령금기·효능군
중복·건기식 상호작용은 자동 판정 범위 밖이며 약사 확인 필요.
"""
from __future__ import annotations

import base64
import csv
import getpass
import hashlib
import hmac
import html
import io
import itertools
import json
import os
import re
import secrets
import sys
import time
import unicodedata
from datetime import datetime, timezone, timedelta
from urllib.parse import unquote

PRODUCT_SOURCE = "https://www.data.go.kr/data/15095677/openapi.do"
DUR_SOURCE = "https://www.data.go.kr/data/15059486/openapi.do"
PRODUCT_BASE = "https://apis.data.go.kr/1471000/DrugPrdtPrmsnInfoService08"
DUR_BASE = "https://apis.data.go.kr/1471000/DURPrdlstInfoService03"
SCHEMA_VERSION = 1


def now():
    return datetime.now(timezone(timedelta(hours=9))).isoformat(timespec="seconds")


def clean(value):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", str(value or "")))).strip()


def norm(value):
    # No substring matching, transliteration, salt removal or fuzzy clinical equivalence.
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", str(value))).casefold()


def names(text):
    # One ingredient per line. Keep qualifiers/salt forms; do not split on commas.
    return list(dict.fromkeys(x.strip() for x in str(text).splitlines() if x.strip()))


def ingredient_suggestions(raw):
    # Only explicitly labelled fields; never treat all excipients as active ingredients.
    found = re.findall(r"성분명\s*[:：]\s*([^;|]+)", str(raw))
    return names("\n".join(clean(x) for x in found))


def duplicates(drugs):
    index = {}
    for drug in drugs:
        if not drug.get("confirmed"):
            continue
        for ingredient in drug.get("ingredients", []):
            key = norm(ingredient)
            if key:
                index.setdefault(key, {"ingredient": ingredient, "products": {}})["products"][drug["uid"]] = drug["name"]
    return [{"ingredient": v["ingredient"], "products": list(v["products"].values()),
             "uids": list(v["products"])} for v in index.values() if len(v["products"]) > 1]


def metric(rows):
    if not rows:
        raise ValueError("검증 행이 없습니다.")
    tp = fp = fn = tn = 0
    for row in rows:
        truth = str(row["expected_duplicate"]).strip()
        if truth not in {"0", "1"}:
            raise ValueError("expected_duplicate는 0 또는 1이어야 합니다.")
        a, b = json.loads(row["ingredients_a"]), json.loads(row["ingredients_b"])
        if not all(isinstance(x, list) and all(isinstance(y, str) for y in x) for x in (a, b)):
            raise ValueError("ingredients_a/b는 문자열 JSON 배열이어야 합니다.")
        if not a or not b or any(not x.strip() for x in a + b):
            raise ValueError("검증용 성분 목록은 비어 있을 수 없습니다.")
        predicted = bool({norm(x) for x in a} & {norm(x) for x in b})
        expected = truth == "1"
        tp += int(predicted and expected)
        fp += int(predicted and not expected)
        fn += int(not predicted and expected)
        tn += int(not predicted and not expected)
    precision = tp / (tp + fp) if tp + fp else None
    recall = tp / (tp + fn) if tp + fn else None
    f1 = 2 * tp / (2 * tp + fp + fn) if 2 * tp + fp + fn else None
    return dict(n=len(rows), TP=tp, FP=fp, FN=fn, TN=tn, precision=precision, recall=recall, F1=f1)


def password_hash(password, salt=None):
    salt = salt or secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 310000).hex()
    return f"pbkdf2_sha256$310000${salt}${digest}"


def password_ok(password, stored):
    try:
        kind, rounds, salt, expected = stored.split("$")
        if kind != "pbkdf2_sha256" or not 100000 <= int(rounds) <= 2000000:
            return False
        actual = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), int(rounds)).hex()
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError):
        return False


def self_test():
    def d(uid, ingredients, confirmed=True):
        return dict(uid=uid, name=uid, ingredients=ingredients, confirmed=confirmed)
    assert len(duplicates([d("a", ["아세트아미노펜", "카페인"]), d("b", [" 아세트아미노펜 "])])) == 1
    assert not duplicates([d("a", ["이부프로펜"]), d("b", ["덱시부프로펜"])])
    assert not duplicates([d("a", ["성분A"]), d("b", ["성분A"], False)])
    assert not duplicates([d("a", ["성분A", "성분A"])])
    assert not duplicates([d("a", ["성분A염산염"]), d("b", ["성분A"])])
    rows = [dict(ingredients_a='["A"]', ingredients_b='["A"]', expected_duplicate="1"),
            dict(ingredients_a='["A"]', ingredients_b='["B"]', expected_duplicate="0"),
            dict(ingredients_a='["C"]', ingredients_b='["C"]', expected_duplicate="0"),
            dict(ingredients_a='["D"]', ingredients_b='["E"]', expected_duplicate="1")]
    r = metric(rows)
    assert (r["TP"], r["FP"], r["FN"], r["TN"]) == (1, 1, 1, 1)
    assert r["precision"] == r["recall"] == r["F1"] == 0.5
    p = password_hash("test-only")
    assert password_ok("test-only", p) and not password_ok("wrong", p)
    assert ingredient_suggestions("성분명 : 가상A; 분량 : 5; 성분명 : 가상B; 분량 : 2") == ["가상A", "가상B"]
    print("PASS: duplication, composite ingredients, unknown, salts, precision/recall/F1, password hash. Synthetic tests only.")


if __name__ == "__main__" and "--hash-password" in sys.argv:
    password = getpass.getpass("계정 비밀번호 (12자 이상 권장): ")
    if len(password) < 12:
        sys.exit("12자 이상을 사용하세요.")
    print(password_hash(password))
    sys.exit(0)
if __name__ == "__main__" and "--self-test" in sys.argv:
    self_test()
    sys.exit(0)

import requests
import streamlit as st
from PIL import Image, ImageOps

st.set_page_config(page_title="약체크 · 구매 전 한 번 더", page_icon="💊", layout="centered", initial_sidebar_state="collapsed")


def setting(key, default=""):
    try:
        return st.secrets.get(key, os.environ.get(key, default))
    except Exception:
        return os.environ.get(key, default)


class ApiError(Exception):
    pass


def api_request(base, operation, params):
    key = str(setting("MFDS_SERVICE_KEY"))
    if not key:
        raise ApiError("공식 API 인증키 미설정 · 공식 조회 불가")
    # Do not include URL/exception details: these may contain the secret key.
    try:
        response = requests.get(f"{base}/{operation}", params={
            "serviceKey": unquote(key), "type": "json", **params}, timeout=(5, 18))
        response.raise_for_status()
        payload = response.json()
    except (requests.RequestException, ValueError):
        raise ApiError("공식 API 연결/응답 오류 · 키 권한, 트래픽 및 서비스 상태를 확인하세요.") from None
    root = payload.get("response", payload)
    header = root.get("header", {})
    if str(header.get("resultCode", "")) not in {"00", "0000", "0"}:
        raise ApiError("공식 API 오류 · 인증키/활용승인/호출 한도를 확인하세요.")
    body = root.get("body", {})
    items = body.get("items", [])
    if isinstance(items, dict):
        items = items.get("item", [])
    if items is None or items == "":
        items = []
    if isinstance(items, dict):
        items = [items]
    if not isinstance(items, list) or not all(isinstance(x, dict) for x in items):
        raise ApiError("예상과 다른 API 스키마 · 자동 판정을 중단합니다.")
    try:
        total = int(body["totalCount"])
    except (KeyError, TypeError, ValueError):
        raise ApiError("응답 건수 확인 불가 · 누락 여부를 판단할 수 없습니다.") from None
    return items, total


def search_products(query, barcode=False, page=1):
    params = {"pageNo": page, "numOfRows": 20}
    params["bar_code" if barcode else "item_name"] = query
    rows, total = api_request(PRODUCT_BASE, "getDrugPrdtPrmsnDtlInq08", params)
    if barcode:
        # Unknown barcode formatting is not accepted as a confirmed match.
        rows = [r for r in rows if query in re.findall(r"\d{8,14}", str(r.get("BAR_CODE", "")))]
    return rows, total


def get_dur(code):
    rows = []
    total = 0
    for page in range(1, 7):
        batch, total = api_request(DUR_BASE, "getUsjntTabooInfoList03", {
            "itemSeq": code, "pageNo": page, "numOfRows": 100})
        # A service ignoring itemSeq must never silently certify the query.
        if any(str(r.get("ITEM_SEQ", "")) != str(code) for r in batch):
            raise ApiError("DUR 품목코드 필터/응답이 일치하지 않습니다. 전문가 확인 필요.")
        rows.extend(batch)
        if len(rows) >= total:
            return {"rows": rows, "complete": True, "count": total, "checked_at": now()}
        if not batch:
            break
    return {"rows": rows, "complete": False, "count": total, "checked_at": now()}


def drug_from_row(row):
    raw = str(row.get("MATERIAL_NAME") or row.get("MAIN_ITEM_INGR") or "")
    code = str(row.get("ITEM_SEQ", ""))
    return dict(uid=secrets.token_hex(8), name=clean(row.get("ITEM_NAME")), code=code,
                company=clean(row.get("ENTP_NAME")), form=clean(row.get("FORM_CODE_NAME") or row.get("CHART")),
                strength="", raw=raw, ingredients=[], confirmed=False, kind="일반의약품",
                source=PRODUCT_SOURCE, updated=clean(row.get("CHANGE_DATE") or row.get("UPDATE_DATE") or "제공되지 않음"),
                retrieved=now(), warnings=clean(row.get("NB_DOC_DATA") or row.get("NB_DOC_ID")),
                demo=False, identification="공식 조회 · 사용자 확인 전")


def run_analysis(drugs):
    result = {"time": now(), "duplicate": duplicates(drugs), "contra": [], "notes": [],
              "coverage": [], "unconfirmed": [], "mechanisms": []}
    for d in drugs:
        if not d.get("confirmed") or not d.get("ingredients"):
            result["unconfirmed"].append(d["name"])
    all_demo = bool(drugs) and all(d.get("demo") for d in drugs)
    if all_demo:
        result["notes"].append("가상 예제: 공식 DUR 조회를 실행하지 않았습니다. 실제 복용 판단에 사용하지 마세요.")
        return result
    real = [d for d in drugs if d.get("code") and not d.get("demo") and d["kind"] != "건강기능식품"]
    for d in drugs:
        if d not in real:
            result["coverage"].append({"name": d["name"], "state": "공식 DUR 미조회 (코드 없음/건기식/가상)", "checked_at": "—"})
    targets = {str(d["code"]): d for d in real}
    seen = set()
    for d in real:
        try:
            data = get_dur(d["code"])
            state = f"조회 완료 · {data['count']}건 (이 앱 범위의 병용금기만)" if data["complete"] else "일부 조회 · 누락 가능"
            result["coverage"].append({"name": d["name"], "state": state, "checked_at": data["checked_at"]})
            for row in data["rows"]:
                other_code = str(row.get("MIXTURE_ITEM_SEQ", ""))
                if not other_code:
                    result["notes"].append(f"{d['name']}: 상대 품목코드 없는 DUR 행은 자동 매칭에서 제외했습니다.")
                    continue
                other = targets.get(other_code)
                if not other or other["uid"] == d["uid"]:
                    continue
                pair = tuple(sorted([d["uid"], other["uid"]]))
                if pair in seen:
                    continue
                seen.add(pair)
                reason = clean(row.get("PROHBT_CONTENT") or row.get("REMARK") or "사유 원문 미제공 · 약사에게 공식 자료 확인 요청")
                result["contra"].append({"products": [d["name"], other["name"]], "uids": list(pair),
                                         "reason": reason, "source": DUR_SOURCE,
                                         "notice_date": clean(row.get("NOTIFICATION_DATE")), "retrieved": data["checked_at"]})
                # Evidence extract only. No inference of enzyme, transporter or ADME pathway.
                sentences = re.split(r"(?<=[.!?。])\s+|\n", reason)
                excerpts = [s for s in sentences if re.search(r"CYP|P-gp|P glycoprotein|수송체|흡수|분포|대사|배설|청소율", s, re.I)]
                if excerpts:
                    result["mechanisms"].append({"products": [d["name"], other["name"]], "quote": " ".join(excerpts), "source": DUR_SOURCE})
        except ApiError as exc:
            result["coverage"].append({"name": d["name"], "state": f"조회 불가 · {exc}", "checked_at": now()})
    result["notes"].append("병용금기 미검출은 상호작용 없음이 아닙니다. 용량·투여경로·기간·질환·임신·연령·건기식·효능군 중복은 약사 확인이 필요합니다.")
    return result


def analysis_signature(member):
    return hashlib.sha256(json.dumps(member, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def clear_analysis():
    st.session_state.pop("result", None)
    st.session_state.pop("result_signature", None)


def persist_add(drug, target):
    member = st.session_state.family[st.session_state.active]
    if sum(len(x) for x in member.values()) >= 12:
        st.error("구성원별 최대 12개입니다. 누락 약이 있으면 상담 시 별도로 전달하세요.")
        return False
    if drug.get("code") and any(d.get("code") == drug["code"] for group in member.values() for d in group):
        st.error("이미 등록한 품목입니다. 기존 항목을 확인하세요.")
        return False
    member[target].append(drug)
    clear_analysis()
    return True


def get_member():
    return st.session_state.family[st.session_state.active]


def public_snapshot():
    return {"schema": SCHEMA_VERSION, "created": now(), "family": st.session_state.family, "active": st.session_state.active}


def encrypt_backup(password):
    from cryptography.fernet import Fernet
    salt = secrets.token_bytes(16)
    key = base64.urlsafe_b64encode(hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 390000, 32))
    return b"YAKCHECK1\n" + salt + Fernet(key).encrypt(json.dumps(public_snapshot(), ensure_ascii=False).encode())


def decrypt_backup(blob, password):
    from cryptography.fernet import Fernet
    prefix = b"YAKCHECK1\n"
    if not blob.startswith(prefix) or len(blob) > 2_000_000:
        raise ValueError("지원하지 않는 백업입니다.")
    salt, cipher = blob[len(prefix):len(prefix) + 16], blob[len(prefix) + 16:]
    key = base64.urlsafe_b64encode(hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 390000, 32))
    data = json.loads(Fernet(key).decrypt(cipher, ttl=None))
    if data.get("schema") != 1 or not isinstance(data.get("family"), dict) or not 1 <= len(data["family"]) <= 8:
        raise ValueError("백업 스키마 오류")
    family = data["family"]
    for alias, groups in family.items():
        if not isinstance(alias, str) or not 1 <= len(alias) <= 20 or set(groups) != {"current", "planned"}:
            raise ValueError("구성원 형식 오류")
        if not all(isinstance(v, list) for v in groups.values()) or sum(map(len, groups.values())) > 12:
            raise ValueError("복약 목록 형식 오류")
        for drug in groups["current"] + groups["planned"]:
            if not isinstance(drug, dict) or not all(k in drug for k in ("uid", "name", "ingredients", "kind", "code")):
                raise ValueError("약 정보 형식 오류")
            if not all(isinstance(drug[k], str) for k in ("uid", "name", "kind", "code")):
                raise ValueError("약 정보 타입 오류")
            if not isinstance(drug["ingredients"], list) or not all(isinstance(x, str) for x in drug["ingredients"]):
                raise ValueError("성분 형식 오류")
            # Imported identification/confirmation cannot be blindly trusted.
            drug["confirmed"] = False
            drug["identification"] = "백업 복원 · 재확인 필요"
    return family


def report_lines(alias, member, result):
    lines = [f"약체크 | 약사 상담 카드 — {alias}", f"작성: {now()}", "진단·처방·복용 허가가 아닌 확인 보조 자료입니다."]
    for group, title in (("current", "복용 중"), ("planned", "구매 예정")):
        lines += [f"[{title}]"]
        if not member[group]:
            lines.append("등록 없음 (미입력 약 여부 확인 필요)")
        for d in member[group]:
            lines += [f"• {d['name']} / {d['kind']} / 품목코드: {d.get('code') or '없음'}",
                      f"  제형: {d.get('form') or '미확인'} | 함량: {d.get('strength') or '미확인'}",
                      f"  성분: {', '.join(d.get('ingredients', [])) or '미확인'} | 사용자 확인: {'완료' if d.get('confirmed') else '필요'}",
                      f"  출처: {d.get('source') or '사용자 입력'} | 갱신: {d.get('updated', '미제공')} | 조회: {d.get('retrieved', '없음')}"]
    if not result:
        lines.append("검사 미실행: 공식 상호작용을 확인하지 않았습니다.")
    else:
        lines += [f"[확인 결과: {result['time']}]"]
        for x in result["duplicate"]:
            lines.append(f"중복 성분: {x['ingredient']} / {' + '.join(x['products'])} (명칭 정확일치; 용량 미평가)")
        for x in result["contra"]:
            lines += [f"공식 병용금기: {' + '.join(x['products'])}", f"근거: {x['reason']}", f"출처: {x['source']} / 조회: {x['retrieved']}"]
        for x in result["coverage"]:
            lines.append(f"조회 범위: {x['name']} / {x['state']} / {x['checked_at']}")
        for x in result["mechanisms"]:
            lines += [f"공식 기전 원문 발췌: {x['quote']}", f"출처: {x['source']}"]
        if not result["mechanisms"]:
            lines.append("ADME/CYP/수송체 기전: 확인한 공식 원문에서 제공되지 않음. 추정하지 않음.")
        if result["unconfirmed"]:
            lines.append("성분 미확인: " + ", ".join(result["unconfirmed"]))
        lines += result["notes"]
    lines += ["[약사에게 확인할 내용]", "1. 모든 처방약·일반약·건기식·필요시 복용약이 포함되었나요?",
              "2. 성분·함량·제형과 투여경로가 정확한가요?", "3. 질환·알레르기·임신/수유·연령·복용량·기간에 추가 주의가 있나요?",
              "임의로 복용을 중단하거나 용량을 변경하지 말고 약사·의사에게 문의하세요.",
              "정보 미검출/미조회는 안전하다는 뜻이 아닙니다.", f"제품 출처: {PRODUCT_SOURCE}", f"DUR 출처: {DUR_SOURCE}"]
    return lines


@st.cache_resource(show_spinner=False)
def pdf_font():
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    # Public font only. No patient information sent. Font licensed under OFL.
    url = "https://raw.githubusercontent.com/google/fonts/main/ofl/nanumgothic/NanumGothic-Regular.ttf"
    try:
        r = requests.get(url, timeout=(4, 12))
        r.raise_for_status()
        pdfmetrics.registerFont(TTFont("YakKorean", io.BytesIO(r.content)))
        return "YakKorean", True
    except Exception:
        from reportlab.pdfbase.cidfonts import UnicodeCIDFont
        pdfmetrics.registerFont(UnicodeCIDFont("HYSMyeongJo-Medium"))
        return "HYSMyeongJo-Medium", False


def make_pdf(lines):
    from reportlab.lib import colors
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
    font, embedded = pdf_font()
    output = io.BytesIO()
    doc = SimpleDocTemplate(output, pagesize=(420, 595), rightMargin=24, leftMargin=24,
                            topMargin=25, bottomMargin=25, title="약사 상담 카드", author="약체크")
    style = ParagraphStyle("body", fontName=font, fontSize=9, leading=14,
                           textColor=colors.HexColor("#172B3A"), wordWrap="CJK", spaceAfter=5)
    story = []
    for i, line in enumerate(lines):
        heading = i == 0 or line.startswith("[")
        styled = ParagraphStyle(f"s{i}", parent=style, fontSize=12 if heading else 9,
                                leading=17 if heading else 14, spaceBefore=8 if heading else 0)
        story.append(Paragraph(html.escape(line), styled))
    if not embedded:
        story += [Spacer(1, 8), Paragraph("한글 대체 폰트 사용: PDF 뷰어에 따라 표시가 다를 수 있습니다.", style)]
    doc.build(story)
    return output.getvalue(), embedded


st.markdown("""<style>
:root{--ink:#172B3A;--teal:#087F8C;--paper:#F5F8FA}
[data-testid="stAppViewContainer"]{background:var(--paper)}
.block-container{max-width:560px;padding:1.1rem .85rem 1rem!important}
header[data-testid="stHeader"]{background:transparent;height:0}
h1,h2,h3,p{color:var(--ink)}
.hero{display:flex;gap:11px;align-items:center;margin:0 0 10px}
.logo{width:46px;height:46px;border-radius:16px;background:#D7F1ED;display:grid;place-items:center;font-size:27px}
.hero b{font-size:23px;letter-spacing:-1px}.hero small{display:block;font-size:12px;color:#526673}
.hint{font-size:11px;color:#536773;line-height:1.45;margin:7px 0}
.status{padding:10px 12px;border-radius:13px;background:#FFF1DE;color:#644214;font-size:13px;border:1px solid #EAC491}
[data-testid="stVerticalBlock"]{gap:.55rem}
.stButton>button,.stDownloadButton>button{border-radius:12px;min-height:42px}
[data-testid="stMetricValue"]{font-size:1.35rem}
[data-testid="stMetricLabel"]{font-size:.73rem}
[data-testid="stCaptionContainer"]{font-size:11px}
@media(max-width:600px){.block-container{padding-top:.6rem!important}.hero{margin-bottom:4px}.hero b{font-size:21px}
[data-testid="stHorizontalBlock"]{gap:.4rem;flex-wrap:nowrap!important}
[data-testid="stColumn"]{min-width:0!important;flex:1!important}
.stButton>button{font-size:12px;padding:.25rem .35rem} [data-testid="stMetricValue"]{font-size:1.1rem}}
/* Browser chrome, zoom, accessibility font sizes and long content vary.
   Never hide overflowing medical warnings to promise zero scrolling. */
</style>""", unsafe_allow_html=True)


if "identity" not in st.session_state:
    st.session_state.identity = None
accounts = setting("accounts", {})


def login_gate():
    st.markdown('<div class="hero"><div class="logo">💊</div><div><b>약체크</b><small>구매 전, 겹치는 성분과 주의사항 확인</small></div></div>', unsafe_allow_html=True)
    st.caption("실제 복약정보는 로그인 후 사용하세요. 키 없이 가상 예제를 체험할 수 있습니다.")
    with st.form("login"):
        username = st.text_input("계정", max_chars=40)
        password = st.text_input("비밀번호", type="password", max_chars=128)
        if st.form_submit_button("🔐 로그인", use_container_width=True):
            wait = st.session_state.get("login_wait", 0)
            if time.time() < wait:
                st.error("잠시 후 다시 시도하세요.")
            else:
                account = accounts.get(username, {}) if accounts else {}
                if account and password_ok(password, str(account.get("password_hash", ""))):
                    role = str(account.get("role", "viewer"))
                    if role not in {"owner", "editor", "viewer"}:
                        role = "viewer"
                    st.session_state.identity = {"user": username, "role": role, "demo": False}
                    st.rerun()
                else:
                    st.session_state.login_wait = time.time() + 3
                    st.error("로그인 정보가 올바르지 않거나 계정이 설정되지 않았습니다.")
    if st.button("🧪 가상 예제 체험", use_container_width=True):
        st.session_state.identity = {"user": "체험", "role": "owner", "demo": True}
        st.rerun()
    with st.expander("⚙️ 배포 설정 · 범위"):
        st.markdown("`app.py` 상단 설명대로 공식 API 키와 해시 비밀번호 계정을 설정하세요. 계정이 없으면 실제 정보 입력을 제한합니다. 이 앱은 의학적 판단을 대신하지 않습니다.")
    st.stop()


if not st.session_state.identity:
    login_gate()
identity = st.session_state.identity
editable = identity["role"] in {"owner", "editor"}
is_owner = identity["role"] == "owner"
is_demo = identity["demo"]
if "family" not in st.session_state:
    st.session_state.family = {"나": {"current": [], "planned": []}}
    st.session_state.active = "나"
    if is_demo:
        def demo_drug(title, ingredients):
            return dict(uid=secrets.token_hex(8), name=title, code="", company="가상", form="가상 정제",
                        strength="각 성분 가상 1단위", raw="가상 데이터", ingredients=ingredients,
                        confirmed=True, kind="일반의약품", source="합성 시험자료 (실제 제품 아님)",
                        updated="해당 없음", retrieved=now(), warnings="", demo=True, identification="가상 예제")
        st.session_state.family["나"] = {
            "current": [demo_drug("[가상] 복합 감기약 A", ["가상성분 α", "가상성분 β"])],
            "planned": [demo_drug("[가상] 단일 진통제 B", ["가상성분 α"])]}


@st.dialog("➕ 의약품 식별 · 등록", width="small")
def add_dialog():
    if not editable or is_demo:
        st.info("체험 모드에서는 가상 목록만 사용합니다. 실제 등록은 계정 설정 후 로그인하세요.")
        return
    target_label = st.segmented_control("등록 위치", ["💊 복용 중", "🛍️ 구매 예정"], default="🛍️ 구매 예정")
    target = "current" if target_label == "💊 복용 중" else "planned"
    method = st.segmented_control("검색 방법", ["🔎 제품명", "📷 사진", "▥ 바코드", "✍️ 직접"], default="🔎 제품명")
    if method in {"📷 사진", "▥ 바코드"}:
        st.caption("포장 사진만 사용하세요. 처방전·이름·주민번호 등 개인정보를 촬영하지 마세요. 사진은 목록에 저장하지 않습니다.")
        source = st.radio("이미지 입력", ["업로드", "촬영"], horizontal=True)
        upload = st.file_uploader("포장 이미지", type=["png", "jpg", "jpeg", "webp"]) if source == "업로드" else st.camera_input("포장 촬영")
        if upload:
            if upload.size > 8_000_000:
                st.error("8MB 이하 이미지를 사용하세요.")
                return
            if method == "▥ 바코드" and st.button("▥ 코드 읽기", use_container_width=True):
                try:
                    import zxingcpp
                    image = ImageOps.exif_transpose(Image.open(upload))
                    if image.width * image.height > 24_000_000:
                        raise ValueError("이미지 해상도가 너무 큽니다.")
                    codes = zxingcpp.read_barcodes(image.convert("RGB"))
                    values = list(dict.fromkeys(x.text for x in codes if re.fullmatch(r"\d{8,14}", x.text)))
                    if not values:
                        st.warning("숫자형 의약품 코드를 인식하지 못했습니다. 아래에 직접 입력하세요.")
                    else:
                        st.session_state.barcode_values = values
                        st.session_state.query_barcode = values[0]
                except Exception:
                    st.error("바코드 인식 실패 · 선명한 이미지 또는 직접 입력을 사용하세요.")
            if method == "📷 사진":
                consent = st.checkbox("사진을 Google Cloud Vision에 전송하는 데 동의합니다. 원문은 이 세션에서만 표시됩니다.")
                if st.button("🔤 OCR 읽기", disabled=not consent, use_container_width=True):
                    key = str(setting("GOOGLE_VISION_API_KEY"))
                    if not key:
                        st.error("GOOGLE_VISION_API_KEY 미설정 · 제품명으로 검색하거나 직접 입력하세요.")
                    else:
                        try:
                            image = ImageOps.exif_transpose(Image.open(upload))
                            if image.width * image.height > 24_000_000:
                                raise ValueError("해상도 제한")
                            image.thumbnail((2000, 2000))
                            buffer = io.BytesIO()
                            image.convert("RGB").save(buffer, format="JPEG", quality=88)
                            response = requests.post("https://vision.googleapis.com/v1/images:annotate",
                                params={"key": key}, json={"requests": [{"image": {"content": base64.b64encode(buffer.getvalue()).decode()},
                                "features": [{"type": "DOCUMENT_TEXT_DETECTION"}], "imageContext": {"languageHints": ["ko", "en"]}}]}, timeout=(5, 25))
                            response.raise_for_status()
                            entry = response.json().get("responses", [{}])[0]
                            if entry.get("error"):
                                raise ValueError("OCR 서비스 오류")
                            st.session_state.ocr_text = entry.get("fullTextAnnotation", {}).get("text", "")[:12000]
                            st.session_state.ocr_source = upload.name
                        except Exception:
                            st.error("OCR 인식 실패 · 이미지, 서비스 키 및 권한을 확인하세요.")
                if st.session_state.get("ocr_text"):
                    st.text_area("OCR 원문 · 제품명/성분/함량을 직접 수정 후 확인", key="ocr_text", height=140)
                    st.info("OCR은 문자 인식 보조입니다. 성분·함량을 약 정보로 자동 확정하지 않습니다. 아래 제품명 검색 후 공식 제품을 선택하세요.")
                    ocr_lines = [x.strip() for x in st.session_state.ocr_text.splitlines() if x.strip()]
                    hints = re.findall(r"\d+(?:\.\d+)?\s*(?:mg|mcg|μg|µg|g|mL|ml|IU|밀리그램|마이크로그램|그램)(?:\s*/\s*(?:정|캡슐|포|mL|ml))?", st.session_state.ocr_text, re.I)
                    st.caption("자동 추출 함량 후보 (확정 아님): " + (" · ".join(dict.fromkeys(hints)) or "미검출"))
                    labelled = ingredient_suggestions(st.session_state.ocr_text)
                    st.caption("자동 추출 성분명 후보 (확정 아님): " + (" · ".join(labelled) or "성분명 라벨 미검출 · 원문에서 직접 확인"))
                    chosen_line = st.selectbox("제품명 후보 · 실제 제품명인 행을 선택 후 수정", ocr_lines or [""], key="ocr_product_hint")
                    if st.button("선택 행을 검색어로 사용"):
                        st.session_state.query_name = chosen_line[:100]
        if method == "▥ 바코드" and len(st.session_state.get("barcode_values", [])) > 1:
            code = st.selectbox("인식된 코드 선택", st.session_state.barcode_values)
            if st.button("이 코드 사용"):
                st.session_state.query_barcode = code
                st.caption("선택한 코드를 아래 검색어에 반영했습니다.")
    manual = method == "✍️ 직접"
    if not manual:
        barcode = method == "▥ 바코드"
        query = st.text_input("바코드 숫자 (GTIN/표준코드)" if barcode else "제품명 · OCR 원문에서 정확히 옮겨 검색",
                              key="query_barcode" if barcode else "query_name", max_chars=100)
        search_page = st.number_input("결과 페이지", min_value=1, max_value=100, value=1, step=1)
        if st.button("🔎 공식 제품 검색", use_container_width=True):
            if not query.strip() or (barcode and not re.fullmatch(r"\d{8,14}", query.strip())):
                st.error("제품명 또는 올바른 숫자 코드를 입력하세요.")
            else:
                try:
                    with st.spinner("공식 허가정보 조회 중…"):
                        rows, total = search_products(query.strip(), barcode, int(search_page))
                    st.session_state.search_rows = rows
                    st.session_state.search_total = total
                    st.session_state.search_context = (method, query.strip(), int(search_page))
                    st.session_state.pop("selected_candidate", None)
                except ApiError as exc:
                    st.session_state.search_rows = []
                    st.error(str(exc))
        context = (method, query.strip(), int(search_page))
        rows = st.session_state.get("search_rows", []) if st.session_state.get("search_context") == context else []
        if rows:
            st.caption(f"전체 검색 {st.session_state.get('search_total')}건 · 현재 표시 {len(rows)}건. 제형/함량/업체가 다른 제품을 구분하세요.")
            selected = st.selectbox("공식 제품 선택", range(len(rows)), format_func=lambda i:
                f"{rows[i].get('ITEM_NAME', '?')} | {rows[i].get('ENTP_NAME', '')} | {rows[i].get('ITEM_SEQ', '')}")
            candidate = drug_from_row(rows[selected])
            if not candidate["code"] or not candidate["name"]:
                st.error("품목 식별정보 누락 · 등록할 수 없습니다.")
                return
            st.caption(f"제공 제형/성상: {candidate['form'] or '미제공'}")
            st.text_area("공식 원료/주성분 원문 · 첨가제를 유효성분에 포함하지 마세요", value=candidate["raw"] or "미제공", disabled=True, height=110)
            edit_form(candidate, target, f"official_{candidate['code']}")
        elif st.session_state.get("search_context") == context:
            st.warning("일치하는 제품을 확인하지 못했습니다. 제품명/제형/함량을 바꾸어 검색하거나 약사에게 확인하세요.")
    else:
        st.warning("직접 입력은 공식 제품 식별이 아닙니다. DUR 조회가 불가능하며 전문가 확인이 필요합니다.")
        candidate = dict(uid=secrets.token_hex(8), name="", code="", company="", form="", strength="", raw="",
                         ingredients=[], confirmed=False, kind="일반의약품", source="사용자 수기 입력", updated="미확인",
                         retrieved=now(), warnings="", demo=False, identification="사용자 수기 입력 · 공식 식별 미확인")
        edit_form(candidate, target, "manual")


def edit_form(candidate, target, widget_id, existing=None):
    with st.form(f"edit_{widget_id}"):
        title = st.text_input("제품명", value=candidate["name"], max_chars=180)
        options = ["일반의약품", "처방의약품", "건강기능식품"]
        kind = st.selectbox("구분", options, index=options.index(candidate.get("kind", "일반의약품")))
        form = st.text_input("제형 · 예: 정제/시럽/서방정", value=candidate.get("form", ""), max_chars=180)
        strength = st.text_input("성분별 함량·단위 · 예: 성분A 10 mg/정", value=candidate.get("strength", ""), max_chars=500)
        ingredients = st.text_area("유효성분만 한 줄에 하나 · 함량은 위 칸에 입력", value="\n".join(candidate.get("ingredients") or ingredient_suggestions(candidate.get("raw", ""))), height=100)
        confirmed = st.checkbox("공식 원문 또는 실제 포장과 대조하여 제품·제형·함량·모든 유효성분을 확인했습니다.", value=False)
        submitted = st.form_submit_button("💾 확인 후 저장", use_container_width=True)
    if submitted:
        values = names(ingredients)
        if not title.strip() or not form.strip() or not strength.strip() or not values or not confirmed:
            st.error("제품명·제형·함량·유효성분을 입력하고 대조 확인해 주세요.")
            return
        if len(values) > 50 or len(ingredients) > 6000:
            st.error("입력량 제한을 초과했습니다.")
            return
        # Editing a code-linked product's identity would invalidate the code mapping.
        if candidate.get("code") and title.strip() != candidate["name"]:
            st.error("공식 제품명은 변경할 수 없습니다. 다른 품목을 검색하세요.")
            return
        candidate.update(name=title.strip(), kind=kind, form=form.strip(), strength=strength.strip(),
                         ingredients=values, confirmed=True, identification="사용자 대조 확인 (전문가 검증 아님)")
        if existing:
            group, uid = existing
            get_member()[group] = [candidate if d["uid"] == uid else d for d in get_member()[group]]
            clear_analysis()
            st.rerun()
        elif persist_add(candidate, target):
            st.rerun()


@st.dialog("👪 가족 · 복용 목록", width="small")
def family_dialog():
    st.caption(f"권한: {identity['role']} · 이 브라우저 세션만 보관 · 실제 이름/생년월일은 입력하지 마세요.")
    if is_owner:
        alias = st.text_input("새 구성원 별칭", max_chars=20)
        if st.button("👤 구성원 추가", disabled=is_demo):
            if alias.strip() and alias.strip() not in st.session_state.family and len(st.session_state.family) < 8:
                st.session_state.family[alias.strip()] = {"current": [], "planned": []}
                st.session_state.active = alias.strip()
                clear_analysis()
                st.rerun()
            else:
                st.warning("중복되지 않는 별칭을 입력하세요. 최대 8명입니다.")
    member = get_member()
    for group, label in (("current", "💊 복용 중"), ("planned", "🛍️ 구매 예정")):
        st.markdown(f"**{label}**")
        if not member[group]:
            st.caption("등록 없음")
        for d in member[group][:]:
            with st.expander(f"{d['name']} · {d['kind']}"):
                st.write("성분: " + (", ".join(d.get("ingredients", [])) or "미확인"))
                st.caption(f"제형 {d.get('form') or '미확인'} / 함량 {d.get('strength') or '미확인'} / 코드 {d.get('code') or '없음'}")
                st.caption(f"출처 {d.get('source', '없음')} / 갱신 {d.get('updated', '미제공')} / 조회 {d.get('retrieved', '없음')}")
                if editable and not is_demo:
                    edit_form(dict(d), group, d["uid"], (group, d["uid"]))
                    confirm_delete = st.checkbox("이 약을 목록에서 삭제", key=f"delconfirm_{d['uid']}")
                    if st.button("🗑️ 삭제", key=f"del_{d['uid']}", disabled=not confirm_delete):
                        member[group] = [x for x in member[group] if x["uid"] != d["uid"]]
                        clear_analysis()
                        st.rerun()
    if is_owner and len(st.session_state.family) > 1 and not is_demo:
        delete_family = st.checkbox("현재 구성원과 복용 목록 전체 삭제에 동의")
        if st.button("현재 구성원 삭제", disabled=not delete_family):
            del st.session_state.family[st.session_state.active]
            st.session_state.active = next(iter(st.session_state.family))
            clear_analysis()
            st.rerun()
    with st.expander("🔐 암호화 백업 · 복원"):
        st.caption("공유 저장소가 아닙니다. 백업을 전달받은 사람은 비밀번호가 있어야 복원할 수 있습니다. 복원 후 모든 약을 재확인해야 합니다.")
        pw = st.text_input("백업 비밀번호 · 12자 이상", type="password", max_chars=128)
        if st.button("암호화 백업 만들기", disabled=len(pw) < 12 or is_demo):
            st.session_state.backup_bytes = encrypt_backup(pw)
        if st.session_state.get("backup_bytes"):
            st.download_button("⬇️ 암호화 파일", st.session_state.backup_bytes, "yakcheck.yak", "application/octet-stream")
        upload = st.file_uploader("백업 복원", type=["yak"])
        replace_ok = st.checkbox("현재 세션의 전체 가족 목록을 덮어씁니다")
        if st.button("복원 실행", disabled=not (upload and replace_ok and pw and is_owner and not is_demo)):
            try:
                family = decrypt_backup(upload.getvalue(), pw)
                st.session_state.family = family
                st.session_state.active = next(iter(family))
                clear_analysis()
                st.rerun()
            except Exception:
                st.error("복원 실패: 비밀번호/파일 형식을 확인하세요. 기존 목록은 유지됩니다.")


@st.dialog("🔍 근거 · 확인 범위", width="small")
def detail_dialog():
    result = st.session_state.get("result")
    if not result:
        st.info("먼저 확인 검사를 실행하세요.")
        return
    st.caption("복용 중끼리, 구매 예정끼리, 두 그룹 사이의 등록된 모든 조합을 검사합니다. 중복은 성분명 정확일치이며 임상적 동등성·용량은 평가하지 않습니다.")
    for x in result["contra"]:
        st.error("⛔ 공식 병용금기 · " + " + ".join(x["products"]))
        st.write(x["reason"])
        st.caption(f"공고일: {x.get('notice_date') or '미제공'} / 조회: {x['retrieved']}")
        st.link_button("공식 DUR 출처", x["source"])
    for x in result["duplicate"]:
        st.warning("⚠️ 동일 성분 · " + x["ingredient"])
        st.write(" + ".join(x["products"]))
        st.caption("등록된 확인 성분 기준입니다. 실제 복용량·제형에 따른 의미는 약사에게 확인하세요.")
    st.markdown("**🧬 ADME · CYP · 수송체**")
    if result["mechanisms"]:
        for x in result["mechanisms"]:
            st.write(" + ".join(x["products"]))
            st.info(x["quote"])
            st.caption("공식 DUR 원문 문장 발췌 · 기전 분류/추론/추가 생성 없음")
    else:
        st.caption("확인한 공식 원문에 기전 정보 없음 또는 미조회. AI로 보충하지 않습니다.")
    st.markdown("**📡 품목별 조회 상태**")
    for x in result["coverage"]:
        st.write(f"• {x['name']}: {x['state']}")
        st.caption(x["checked_at"])
    if result["unconfirmed"]:
        st.warning("성분 재확인 필요: " + ", ".join(result["unconfirmed"]))
    for note in result["notes"]:
        st.info(note)
    st.warning("추가 복용 여부·중단·용량 변경은 약사/의사에게 문의하세요. 호흡곤란·의식저하 등 응급 증상은 119로 도움을 요청하세요.")


@st.dialog("📄 약사 상담 카드", width="small")
def report_dialog():
    st.caption("실제 이름을 넣지 않은 별칭 기반 자료입니다. 공유 전 민감정보를 확인하세요. PDF는 기기 내 저장 후 직접 전달합니다.")
    lines = report_lines(st.session_state.active, get_member(), st.session_state.get("result"))
    st.text_area("상담 요약 미리보기", "\n".join(lines), height=260, disabled=True)
    if st.button("📄 PDF 생성", use_container_width=True):
        try:
            with st.spinner("한글 PDF 생성 중…"):
                data, embedded = make_pdf(lines)
            st.session_state.pdf_bytes = data
            st.session_state.pdf_signature = hashlib.sha256("\n".join([lines[0]] + lines[2:]).encode()).hexdigest()
            if not embedded:
                st.warning("한글 대체 폰트로 생성했습니다. 다운로드 후 표시 상태를 확인하세요.")
        except Exception:
            st.error("PDF 생성 실패 · 아래 텍스트 요약을 사용할 수 있습니다.")
    signature = hashlib.sha256("\n".join([lines[0]] + lines[2:]).encode()).hexdigest()
    if st.session_state.get("pdf_bytes") and st.session_state.get("pdf_signature") == signature:
        st.download_button("⬇️ 상담 PDF", st.session_state.pdf_bytes, "yakcheck-consultation.pdf", "application/pdf", use_container_width=True)
    st.download_button("⬇️ 텍스트 요약", "\n".join(lines), "yakcheck-consultation.txt", "text/plain;charset=utf-8", use_container_width=True)


@st.dialog("⚙️ 출처 · 검증 · 도움말", width="small")
def help_dialog():
    st.markdown("**공식 데이터**")
    st.link_button("식약처 제품 허가정보", PRODUCT_SOURCE)
    st.link_button("식약처 DUR 품목정보", DUR_SOURCE)
    st.caption("품목별 원문 갱신일이 없으면 미제공으로 표시합니다. 조회 시각은 자료 개정일이 아닙니다. 공식 API 결과를 이 앱이 임상적으로 검증했다는 뜻은 아닙니다.")
    st.markdown("**등록과 확인**")
    st.write("① 제품명/사진/바코드 → ② 공식 제품 선택 → ③ 제형·함량·유효성분 대조 → ④ 복용 중/구매 예정 등록 → ⑤ 검사 → ⑥ 약사 상담")
    st.write("OCR은 사진의 제품명·성분·함량 문자 인식을 보조합니다. 구조화·성분 확정은 사용자 확인이 필요합니다. 염/수화물·한영 동의어는 자동 통합하지 않아 미탐지할 수 있습니다. 건기식은 공식 DUR 자동 판정 대상이 아닙니다.")
    st.caption("실사용 목록은 세션 한정입니다. owner/editor/viewer 권한은 현재 로그인 계정에 적용됩니다. 가족별 로그인 공유 저장소는 없습니다. 민감정보는 최소 수집하고 공용 기기에서는 반드시 로그아웃하세요.")
    st.markdown("**📊 중복 탐지 정확도 평가**")
    st.write("식약처 원문을 대조한 제품쌍별 정답을 전문가가 작성한 뒤 업로드하세요. 성분 입력 정확도·동의어 미탐지까지 반영하려면 실제 앱 추출/확인 성분을 입력값으로 사용하세요. 이 평가는 중복 성분 로직만 대상으로 하며 DUR/OCR 임상 성능 지표가 아닙니다.")
    template = io.StringIO()
    writer = csv.DictWriter(template, fieldnames=["case_id", "product_code_a", "product_code_b", "source", "verified_date", "ingredients_a", "ingredients_b", "expected_duplicate"])
    writer.writeheader()
    # Template synthetic data intentionally not presented as official validation.
    writer.writerow(dict(case_id="synthetic-example", product_code_a="가상A", product_code_b="가상B", source="가상 예제·교체 필요", verified_date="", ingredients_a='["가상성분 α"]', ingredients_b='["가상성분 α", "가상성분 β"]', expected_duplicate="1"))
    st.download_button("검증 CSV 양식 (가상 행을 교체하세요)", template.getvalue().encode("utf-8-sig"), "validation-template.csv", "text/csv")
    uploaded = st.file_uploader("전문가 검증 CSV · UTF-8", type=["csv"])
    if uploaded and st.button("정밀도 · 재현율 · F1 계산"):
        try:
            if uploaded.size > 2_000_000:
                raise ValueError("CSV는 2MB 이하여야 합니다.")
            rows = list(csv.DictReader(io.StringIO(uploaded.getvalue().decode("utf-8-sig"))))
            if len(rows) > 10000:
                raise ValueError("최대 10,000행입니다.")
            if not rows or any(not all(str(r.get(k, "")).strip() for k in ("case_id", "product_code_a", "product_code_b", "source", "verified_date")) for r in rows):
                raise ValueError("제품코드·출처·검증일·case_id를 모든 행에 기록하세요.")
            if len({r["case_id"] for r in rows}) != len(rows):
                raise ValueError("중복 case_id가 있습니다.")
            r = metric(rows)
            st.json(r)
            st.caption("null은 분모 0으로 계산 불가입니다. 표본 대표성·누락·정답 품질을 별도로 검토하세요. 업로드 출처를 앱이 독립 검증하지는 않습니다.")
        except (ValueError, KeyError, UnicodeError, TypeError) as exc:
            st.error("평가 실패: " + str(exc))
    if st.button("🔒 로그아웃 · 세션 정보 지우기", use_container_width=True):
        for key in list(st.session_state):
            del st.session_state[key]
        st.rerun()


# Single-screen home: three compact action buttons, internally scrollable list,
# one prominent check button, compact results, dialog-only details.
st.markdown('<div class="hero"><div class="logo">💊</div><div><b>약체크</b><small>일반약 구매 전 · 성분 중복과 공식 병용금기 확인</small></div></div>', unsafe_allow_html=True)
a, b = st.columns([3, 1])
with a:
    active = st.selectbox("가족 별칭", list(st.session_state.family), index=list(st.session_state.family).index(st.session_state.active), label_visibility="collapsed")
    if active != st.session_state.active:
        st.session_state.active = active
        clear_analysis()
        st.rerun()
with b:
    if st.button("⚙️ 도움", use_container_width=True):
        help_dialog()

if is_demo:
    st.caption("🧪 가상 예제 · 실제 의약품/복용 판단에 사용 불가")
else:
    st.caption("📡 공식 조회 설정됨 · 결과별 연결상태 확인" if setting("MFDS_SERVICE_KEY") else "📴 공식 조회 미설정 · 수기 성분 비교만 가능")

c1, c2, c3 = st.columns(3)
with c1:
    if st.button("➕ 약 추가", use_container_width=True, disabled=not editable):
        add_dialog()
with c2:
    if st.button("👪 목록", use_container_width=True):
        family_dialog()
with c3:
    if st.button("📄 상담", use_container_width=True):
        report_dialog()

member = get_member()
with st.container(height=145, border=True):
    for group, icon, label in (("current", "💊", "복용 중"), ("planned", "🛍️", "구매 예정")):
        text = " · ".join(d["name"] + (" ⚠" if not d.get("confirmed") else "") for d in member[group]) or "등록된 약 없음"
        st.markdown(f"**{icon} {label} {len(member[group])}**")
        st.caption(text)

all_drugs = member["current"] + member["planned"]
if st.button("🛡️ 중복 · 공식 병용금기 확인", type="primary", use_container_width=True, disabled=len(all_drugs) < 2):
    with st.spinner("등록된 전체 조합 확인 중…"):
        st.session_state.result = run_analysis(all_drugs)
        st.session_state.result_signature = analysis_signature(member)

result = st.session_state.get("result")
if result and st.session_state.get("result_signature") != analysis_signature(member):
    clear_analysis()
    result = None
if result:
    r1, r2, r3 = st.columns(3)
    with r1:
        st.metric("⚠️ 중복 성분", len(result["duplicate"]))
    with r2:
        st.metric("⛔ 병용금기", len(result["contra"]))
    with r3:
        st.metric("📡 조회 불완전", sum(not x["state"].startswith("조회 완료") for x in result["coverage"]))
    if result["contra"]:
        message = "⛔ 공식 병용금기 확인 · 추가 복용 전 약사에게 확인하세요."
    elif result["duplicate"]:
        message = "⚠️ 동일 성분 확인 · 실제 용량과 병용 여부는 약사 상담이 필요합니다."
    else:
        message = "🔎 등록 정보에서 중복·병용금기 미검출 · 안전 판정이 아닙니다."
    st.markdown(f'<div class="status">{html.escape(message)}</div>', unsafe_allow_html=True)
    if st.button("🔍 근거 · 미조회 항목 · 기전", use_container_width=True):
        detail_dialog()
else:
    st.markdown('<div class="status">🔎 복용 중인 약과 구매할 약을 등록하세요.<br>사진 인식 후에도 제품·제형·함량을 확인해야 합니다.</div>', unsafe_allow_html=True)
st.markdown('<div class="hint">정보 없음은 안전을 뜻하지 않습니다. 미등록 약·건기식도 약사에게 알려주세요.<br>복용 중단·용량 변경은 약사·의사와 결정하세요. 세션 종료 시 목록이 사라질 수 있습니다.</div>', unsafe_allow_html=True)
