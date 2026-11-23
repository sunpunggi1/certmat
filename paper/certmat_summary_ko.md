# CertMat 연구 최종 요약 보고서 (한국어)

**프로젝트명**: `CertMat` (Certified Robust Phase & Elastic Stability Verifier)  
**작업 경로**: `C:\Users\USER\.gemini\antigravity\scratch\certmat`

---

## 1. 연구 개요 및 핵심 성과

AI 신소재 탐색(GNoME, Matbench Discovery WBM)과 공개 DFT 재료 데이터베이스(NIST JARVIS-DFT 3D)는 수십만-수백만 개의 후보 결정 구조를 생성하지만, 기존 안정성 판별은 DFT·ML 에너지/강성 예측 오차를 무시한 부동소수점 점추정(point estimate)에 의존해 왔습니다.

**CertMat**은 확률 근사가 아닌 **정확한 유리수 증명서(Exact Rational Certificate, $\mathbb{Q}$)**와 **기계 컴파일된 Lean 4 형식 검증 커널(`leanprover/lean4:v4.16.0`, 외부 Mathlib 의존성 없음, 51개 핵심 정리 `#print axioms` 표준 공리 전용·`sorryAx` 0건)**을 결합하여 상평형(Convex Hull)과 탄성(Born) 안정성의 최악 강건성을 형식 인증했습니다. 실제 무료 공개 DB **총 1,044,460개 고유 결정상(매칭 PBE-r2SCAN 재감사 234,086회 포함 시 상평형 1,278,545회 경쟁 LP 감사 + 미경쟁 단원소 1건) 및 34,323개 6x6 탄성 텐서(총 1,312,869회 평가)**를 전수 감사하고, 직렬화한 **95,348건의 정확한 유리수 TSV 증명서 전수**를 컴파일된 Lean 4 바이너리(`certmat-check.exe`)와 독립 순수 `Fraction` 검증기로 100.0% 교차 검증했습니다(실패 0건).

---

## 2. 핵심 구현 요약 (4대 정리·엔진·적대적 교차심사 반영)

| 구분 | 구성 파일 | 핵심 내용 | 검증 상태 |
| :--- | :--- | :--- | :--- |
| **Lean 4 형식 증명 커널** | `lean/CertMat/{ExactRat,Farkas,RefErrorCancel,IntervalHull,BornElastic,Checker}.lean`, `lean/Main.lean` | 정리 1(Farkas 쌍대 건전성, 음수 여유 $\delta < 0$ 엄격 차단), 정리 2(원소 기준 오차 $\sum c_{ie}\delta\mu_e$ 완전 상쇄), 정리 3(이질적 구간 $[L_i, U_i]$ 최악 강건성 및 취약점 증인), 정리 4(유리수 $LDL^T$ Born 양정치·반례 벡터·Voigt/SO(3)-불변 Mandel 순수 유리수 Frobenius-Weyl 강건 정리 및 양방향 랭크-1 취약 반례) | `lake build` + `certmat-check.exe` 빌드 완료, **51/51 핵심 정리 `#print axioms` 표준 공리 전용(`sorryAx` 0건)**, 커널·`Main.lean` 금지 키워드 0건 |
| **정확한 유리수 / Z3 감사 엔진** | `certmat/{exact_lp,phase_audit,elastic_audit,uncertainty,lean_bridge,datasets}.py` | HiGHS 기저 탐색 + 순수 `Fraction` 가우스-조르당 복원 + 퇴화/동률 시 Z3 SMT 정확 폴백(전체 LP의 1.37%), Charnes-Cooper 선형분수계획 기반 $\varepsilon^*(x)$ (부분/전체 0-가중치 경계·도달불가 양가중 경쟁상 1x 박스 쌍대 복원 포함) 및 Phase Switching 검출, Voigt/SO(3)-불변 Mandel 양방향 Weyl 증명서 및 VASP/축치환 대칭성 감사, 데이터셋 SHA-256 소스 고정 | `pytest` 15/15 통과(100%), 12종 전체 유효 증명서 + 30종 구문/의미 변조·음수 $\delta$·0-가중치 반례 차분 검증 통과 |
| **대규모 공개 DB 전수 감사** | `scripts/run_full_audit.py`, `scripts/run_supplementary_analysis.py` | GNoME PBE(554,054), GNoME r2SCAN(139,541), 매칭 PBE-r2SCAN(117,043 x 2), JARVIS-DFT 3D 상평형(93,902) 및 탄성(34,323), WBM(256,963) 전수 감사 + 원소 기준 $\sigma_{\text{elem}}=0$ 절제 실험 + 화학계 클러스터 부트스트랩(1,000회) + 지도학습 로지스틱 베이스라인 | **100.0% 정확 검증**, Lean 4 `certmat-check.exe` **95,348 / 95,348건 통과**, 8개 TSV 층화 표본 원본 DB 전체 벡터·원소기저·36원소 바인딩 **540 / 540건 100% 일치** |
| **적대적 교차 심사 및 재현 패키지** | `reproduce_all.py`, `paper/certmat_paper.md`, `paper/certmat_summary_ko.md` | 로컬 읽기 전용 `Claude` CLI 및 `Codex` CLI 적대적 피어 리뷰 + 독립 최종 리뷰에서 지적된 수학·Lean·코드·통계·재현성 약점 전수 수정 후 전체 파이프라인 처음부터 끝까지 재실행 및 SHA-256 잠금(`results/reproduction_manifest.json`) | `reproduce_all.py --full` 및 `--verify-only` 전체 통과 (안전 기본 워커 상한 `--workers 2`, `run_supplementary_analysis.py` 포함 일관 전달) |

---

## 3. 실제 공개 DB 전수 감사 핵심 발견 (4대 헤드라인 결과)

### 발견 1: GNoME PBE vs r2SCAN 117,043개 실측 교차검증 및 정리 2 실증
- **정리 2 실증 (원소 기준 오차의 대량 상쇄)**: 117,043개 매칭 결정에서 `r2SCAN - PBE` 원시 오차 MAE는 **78.90 meV/atom**(RMSE 101.03 meV/atom)이지만, 원소 기준 이동 $\sum c_{ie}\delta\mu_e$가 전체 분산의 **$R^2 = 73.51\%$**를 상쇄하여 비상관 잔차 $\eta_i$ MAE는 **30.96 meV/atom**으로 **60.76% 감소**했습니다.
- **화학군별 극심한 이질성 및 커버리지 진단**: 잔차 MAE는 `intermetallic`(19.93 meV) 대비 `ggau_oxide_fluoride`(94.65 meV)가 **4.75배** 크며, 실제 r2SCAN 전복률(`>0`)은 **7.16% vs 39.09%**, 심각 전복(`>25 meV`)은 **0.30% vs 18.28%(60배 격차)**였습니다. 한편 사전 문헌 구간(`10-55 meV`)의 OOS 잔차 커버리지는 전체 72.92%이나 산화물 군은 33.29-35.07%에 그쳐, OOS p75(74.97%)·p90(89.99%) 보정의 필요성을 실증했습니다.
- **정확 LP vs 외부 프록시 분리 검증**:
  - **동일 117k 1:1 매칭 정확 LP Sub-Hull (116,877 안정상, 5,231 전복)**: 이질적 모델 기준 Robust 전복률 **0.46%** vs Fragile **11.36%**(상대위험도 **24.65배**, 재현율 **93.50%**, ROC-AUC **0.8948**; 균일 25 meV **22.84배**, ROC-AUC **0.8969**; 단조성 위반 0건). 9,989개 결정(9,450개 고유 화학계) GroupKFold 정확 LP(고정 카탈로그 전이형 Hull, $\sigma$ held-out)에서 OOS MAE 보정은 상대위험도 **31.59배**(Robust 0.41% vs Fragile 12.90%)를 달성했으나, 균일 마진 대비 $\Delta\text{AUC}$(+0.0017, 클러스터 부트스트랩 95% CI $[-0.0002, +0.0037]$)는 통계적으로 유의하지 않았습니다(원소 기준 $\sigma_{\text{elem}}=0$ 절제 시에도 27.79배, AUC 0.8966으로 일관).
  - **공식 외부 `Decomposition Energy Per Atom` 프록시(116,988 안정상, 비인증 프록시)**: 문헌 이질적 모델의 Robust 전복률은 **3.00%** vs Fragile **15.33%**(상대위험도 **5.10배**, 재현율 **96.40%**; `... MP` 컬럼 기준 **6.20배**, 재현율 **97.46%**). 화학계 GroupKFold OOS 잔차 보정은 균일 프록시 대비 일반 전복 **0.7061 -> 0.7242**($\Delta=+0.0180$, 클러스터 CI $[+0.0162, +0.0200]$), 심각 전복 **0.5959 -> 0.6402**($\Delta=+0.0443$, 클러스터 CI $[+0.0404, +0.0482]$)로 유의하게 개선되었습니다. 실제 r2SCAN 전복 라벨로 직접 학습한 지도학습 베이스라인(`log1p(margin) + 화학군 원핫` 로지스틱)은 **0.7388 / 0.7270**에 도달하나, CertMat은 전복 라벨 없이 최악 경우 형식 증명서를 제공합니다.
- **GNoME PBE 전체 554,054개 및 r2SCAN 139,541개 현황**: GNoME PBE 공식 외부 여유 중앙값은 `Decomp Energy` 24.0 meV(25 meV 취약 77.38%), `MP` 21.7 meV(80.34%), `MP OQMD` 15.5 meV(88.68%)입니다. GNoME PBE 내부 Hull 불안정 137,970건 중 **99.60%**가 1 meV 이내 근접상이며(중앙값 0.309 meV, p95 0.900 meV, 최대 1.117 meV, 나머지 0.40%는 CSV 소수 4자리 반올림 영향, `Decomposition Energy Per Atom All` 대비 단조성 위반 0건), 명목 안정 416,084건 중 **12,461건(2.99%)**에서 Phase Switching(치명적 역전 59건, 최대 34.48% 과대추정 `a403464fde`)이 검출되었습니다. GNoME r2SCAN 전수에서는 명목 안정 131,784건 중 **4,552건(3.45%)**에서 Phase Switching(치명적 역전 27건, 최대 50.52% `32d32e7908`, 단조성 위반 0건)이 확인되었습니다.

### 발견 2: NIST JARVIS-DFT 3D 공식 `ehull` 컬럼의 대규모 단위 결함 및 원소 절제 검증
- 93,902개 JARVIS-DFT 3D 결정(경쟁상 보유 93,901개 + 미경쟁 단원소 1개 분리)의 정확한 OptB88vdW Convex Hull을 재구축한 결과, 25,908개 명목 안정상 중 25 meV 기준 **69.76%(18,074개)**, 기본 이질적 모델 기준 **76.06%(19,706개)**가 Fragile이었습니다. 원소 기준 오차 $\sigma_{\text{elem}}=0$ 절제 실험에서도 Fragile 비율은 **75.36%(19,524개, 차이 -0.70%p)**로 유지되었고, Phase Switching은 오히려 **921건(3.55%) -> 1,232건(4.76%)**으로 증가했습니다.
- **공식 Figshare `ehull` 이중 나눗셈 결함 및 음성대조군 검증**: 최신 공식 `jdft_3d-9-24-2025.json`(Figshare Article `6815699` / File ID `64391379`, 2026년 11월 기준 `usnistgov/jarvis` 미보고 이슈)의 **63,386개 결정**(안정상 25,908개 중 16,898개·65.22% 포함)에서 `ehull > 1.0 eV/atom`으로 부풀려진 결함을 확인했습니다. 92,955개 다원계에서 $(E_{\text{optB88}}/N_{\text{fu}}) - E_{\text{elem\_hull}}$ 모델은 공개 `ehull`과 **잔차 중앙값 0.00677 eV(84.72%가 0.05 eV 이내 일치)**를 보인 반면, 두 음성대조군($N_{\text{fu}}$ 미나눗셈 2.605 eV·0.95% 일치, 무작위 원소 기준 2.108 eV·1.20% 일치)은 0.95%-1.20% 일치에 그쳐 이중 나눗셈 원인 가설을 강력히 뒷받침했습니다(제보 초안: [jarvis_issue_draft.md](jarvis_issue_draft.md), 최소 재현 스크립트: [repro_jarvis_ehull_bug.py](../scripts/repro_jarvis_ehull_bug.py)). 반면 `formation_energy_peratom`과 `optb88vdw_total_energy`로 구축한 정확 Hull 간 여유 차이는 1,000개 층화 표본에서 중앙값 **0.005 meV/atom**이었습니다.

### 발견 3: NIST JARVIS-DFT 3D 34,323개 6x6 탄성 텐서 전수 감사 (Voigt + SO(3)-불변 Mandel)
- 유효 6x6 탄성 텐서 **34,323개**(비정상 179개 제외) 전수에 대해 **65,348건의 Lean 4 증명서**(`39,619` Voigt 최고 통과 임계치 + 최초 실패 `WEYL_FRAGILE` 반례, `25,729` 순수 유리수 SO(3)-불변 Mandel 최고 통과 `MANDEL_WEYL_ROBUST` 22,531건 + 최초 실패 `MANDEL_WEYL_FRAGILE` 3,198건)를 `certmat-check.exe`로 100.0% 검증했습니다.
- **Born 양정치성**: **22,842개(66.55%)** Born 안정, **11,481개(33.45%)** Born 불안정(수치 발산 `<-1000 GPa`은 267건·2.3%뿐이며 나머지 97.7%는 경미-심각 기계적 불안정).
- **Weyl 섭동 강건성**: 회전 불변인 **Mandel/Kelvin 기준** Born 안정 22,842개 중 1/5/10 GPa 강건 결정은 **22,531 / 21,325 / 19,644개**(Lean `MANDEL_WEYL_ROBUST` 인증), 취약 결정은 **311개(1.36%) / 1,517개(6.64%) / 3,198개(14.00%)**(전원 Lean `MANDEL_WEYL_FRAGILE` 순수 유리수 랭크-1 섭동 반례 인증)이며, 비제약 **Voigt 기준**에서는 **490개(2.15%) / 2,643개(11.57%) / 5,296개(23.19%)**가 취약(전원 Lean `WEYL_FRAGILE` 랭크-1 섭동 반례 인증)했습니다.
- **결정계 대칭성 감사**: VASP OUTCAR 전단 순서 및 단사정계 $a$-고유축·축치환·능면체 [111] 설정을 반영해 **고정 표준축 위반(5,606개; Born-PD 2,358개)**과 **축치환 허용 위반(2,805개·8.17%; Born-PD 401개·1.76%)**, 그리고 좌표계 무관 **입방정 Mandel 축퇴 위반(1,442/9,096; Born-PD 205/6,232·3.29%)**을 병행 보고했습니다.

### 발견 4: Matbench Discovery WBM 256,963개 전수 감사 (배치 Hull 붕괴 세분화)
- 정적 MP2020 Hull 기준 안정으로 보고된 WBM 후보 **42,688개** 중 **19,894개(46.60%)**가 외부 MP 상 추가 전 WBM 내부 상호 경합만으로 엄격 불안정으로 붕괴하며, 이 중 **12,372개(62.19%)는 동일 조성 저에너지 동질이상**, **7,522개(37.81%)는 교차 조성 분해**에 기인합니다. 고유 프로토타입 중복 제거 후(32,805개)에도 **13,385개(40.80%)**가 붕괴하며, 전체 42,688개 중 **38,296개(89.71%)**가 이질적 강건 안정 기준을 통과하지 못합니다.
- MP2020 보정치의 정리 2 직교 분해 결과 $R^2 = 85.04\%$가 원소 기준 이동으로 상쇄되나 `ggau_oxide_fluoride`에는 **279.99 meV/atom MAE**의 비상쇄 잔차가 잔존합니다.

---

## 4. 적대적 교차심사 반영 요약 및 재현 방법

로컬 `Claude` CLI(읽기 전용) 및 `Codex` CLI(`-s read-only`) 적대적 교차 심사를 수행하여 지적된 핵심 결함을 전수 수정했습니다:
1. **Lean 4 커널 및 `certmat-check` 강화**: `checkDualStable` / `INTERVAL_STABLE`에 `delta >= 0` 검증 추가(음수 `delta` 위조 차단), 순수 유리수 가중 코시-슈바르츠(`weighted_cauchy_schwarz`) 및 SO(3)-불변 Mandel 양방향 Frobenius-Weyl 정리(`checkMandelWeylRobustBorn_frob_sound`, `checkMandelWeylFragile_sound`) 기계 증명(총 51개 정리 `#print axioms` 검증).
2. **Python 솔버·무결성·보완분석 강화**: `exact_lp.py` 부분/전체 0-가중치 경계 반례(Codex #2, Claude P1/P2) 및 도달 불가 양의 가중치 경쟁상 1x 박스 쌍대 증명서 생성 버그 수정, `phase_audit.py` 0-분모 동률 Phase Switching 및 화학식 파서 검증 강화, `elastic_audit.py` 빈/비대칭 행렬 거부 및 `MANDEL_WEYL_FRAGILE` 발급, `datasets.py` SHA-256 소스 고정, `reproduce_all.py` 증분 `lake build` 최신성 강제·필수 산출물 fail-closed 잠금·중첩 Lean 주석 파서·전체 벡터/36원소 바인딩 540건 검증, `run_supplementary_analysis.py` `--workers` 일관 전달·화학계 클러스터 부트스트랩(1,000회)·로지스틱 베이스라인·JARVIS/GNoME $\sigma_{\text{elem}}=0$ 절제 실험 추가.
3. **논문 검증 범위 투명화 및 자동 회귀 테스트**: Lean TCB 범위, 내부 카탈로그 상한성, 전이형 Hull GroupKFold 성격, Voigt vs Mandel 양방향 인증을 과장 없이 정확히 기술하고 `pytest`에 논문-JSON 자동 정합성 검증 추가.

```bash
# 1) 모든 데이터셋·Lean 최신성/51정리 공리·95,348건 TSV 증명서·540건 층화 표본 바인딩·pytest 원클릭 검증
.venv\Scripts\python.exe reproduce_all.py --verify-only

# 2) 전체 처음부터 재실행 (안전 기본값: --workers 2; 유휴 시 명시 조정 가능)
.venv\Scripts\python.exe reproduce_all.py --full --workers 2

# 3) 논문용 고해상도 Figure 5종 재생성 및 JARVIS ehull 결함 최소 재현
.venv\Scripts\python.exe scripts/generate_figures.py
.venv\Scripts\python.exe scripts/repro_jarvis_ehull_bug.py
```

### 추가 공개·투고 패키지
- **영문 논문(Markdown & LaTeX/BibTeX)**: [certmat_paper.md](certmat_paper.md), [certmat_paper.tex](certmat_paper.tex), [references.bib](references.bib)
- **고해상도 논문 Figure 5종 (300 DPI PNG + 벡터 PDF)**: `paper/figures/fig1`-`fig5`
- **NIST JARVIS GitHub 제보 초안**: [jarvis_issue_draft.md](jarvis_issue_draft.md)
- **GitHub 공개 대문**: [README.md](../README.md)
