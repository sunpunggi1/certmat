"""
CertMat 논문 및 GitHub README용 고해상도 출판 품질 Figure 5종(PNG 300 DPI + 벡터 PDF)을 생성하는 스크립트.

모든 수치는 `results/*.json` 및 `data/jdft_3d.json`에서 직접 읽어와 시각화합니다.

사용법:
    .venv\\Scripts\\python.exe scripts/generate_figures.py
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import numpy as np

ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.phase_audit import parse_formula_counts

RESULTS_DIR = ROOT_DIR / "results"
FIG_DIR = ROOT_DIR / "paper" / "figures"

# 출판용 전역 스타일 설정
plt.rcParams.update(
    {
        "font.family": "DejaVu Sans",
        "font.size": 10,
        "axes.titlesize": 11.5,
        "axes.titleweight": "bold",
        "axes.labelsize": 10,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 8.8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "figure.facecolor": "white",
        "axes.facecolor": "white",
        "savefig.dpi": 300,
        "pdf.fonttype": 42,
    }
)


def _save_fig(fig: plt.Figure, stem: str) -> None:
    """그림을 `paper/figures/`에 300 DPI PNG와 벡터 PDF로 동시 저장한다."""
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    png_path = FIG_DIR / f"{stem}.png"
    pdf_path = FIG_DIR / f"{stem}.pdf"
    fig.savefig(png_path, dpi=300, bbox_inches="tight", pad_inches=0.12)
    fig.savefig(pdf_path, bbox_inches="tight", pad_inches=0.12)
    plt.close(fig)
    print(f"[그림 저장] {png_path.name} ({png_path.stat().st_size / 1024:.1f} KB) + {pdf_path.name}")


def generate_fig1_gnome_theorem2_and_crossval() -> None:
    """Figure 1: GNoME PBE vs r2SCAN 정리 2 화학군별 잔차·전복률 및 Robust/Fragile 교차검증."""
    gc = json.loads((RESULTS_DIR / "gnome_crossval_summary.json").read_text(encoding="utf-8"))
    sa = json.loads((RESULTS_DIR / "supplementary_analysis.json").read_text(encoding="utf-8"))

    t2 = gc["theorem2_pbe_vs_r2scan_decomposition"]
    res_stats = t2["class_residual_stats"]
    ext_by_cls = gc["external_proxy_validation_decomp_energy"]["by_chemistry_class"]

    cls_labels = {
        "intermetallic": "Intermetallic",
        "f_block_non_oxide": "f-Block\nNon-Oxide",
        "chalcogenide_pnictide": "Chalcogenide /\nPnictide",
        "tm_non_oxide": "TM\nNon-Oxide",
        "halide_oxide_main": "Main-Group\nHalide / Oxide",
        "f_block_oxide_fluoride": "f-Block\nOxide / Fl.",
        "ggau_oxide_fluoride": "GGA+U\nOxide / Fl.",
    }
    ordered_cls = sorted(res_stats.keys(), key=lambda c: res_stats[c]["mae_mev"])
    names = [cls_labels[c] for c in ordered_cls]
    maes = [res_stats[c]["mae_mev"] for c in ordered_cls]
    flip0 = [ext_by_cls[c]["flip_rate_gt0_pct"] for c in ordered_cls]
    flip25 = [ext_by_cls[c]["flip_rate_gt25_pct"] for c in ordered_cls]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.6, 5.2), gridspec_kw={"width_ratios": [1.12, 1.0]})

    # 패널 (a): 화학군별 잔차 MAE vs r2SCAN 전복률
    x = np.arange(len(ordered_cls))
    bars = ax1.bar(x, maes, width=0.56, color="#4C78A8", alpha=0.88, label="Residual η MAE (meV/atom)", zorder=2)
    ax1.set_xticks(x)
    ax1.set_xticklabels(names, fontsize=8.5)
    ax1.set_ylabel("Irreducible Residual η MAE (meV/atom)", color="#2B4C7E")
    ax1.set_ylim(0, 114)
    ax1.grid(axis="y", linestyle="--", alpha=0.35, zorder=0)
    ax1.set_title("(a) Theorem 2 Residual Heterogeneity vs. Real r2SCAN Flips", pad=10)

    for b, val in zip(bars, maes):
        ax1.text(
            b.get_x() + b.get_width() / 2,
            max(4.0, val * 0.48),
            f"{val:.1f}",
            ha="center",
            va="center",
            fontsize=8.2,
            color="white",
            fontweight="bold",
        )

    ax1r = ax1.twinx()
    ax1r.spines["top"].set_visible(False)
    l1 = ax1r.plot(x, flip0, marker="o", linewidth=2.0, markersize=6, color="#D62728", label="Real r2SCAN flip (>0 meV, %)", zorder=4)
    l2 = ax1r.plot(x, flip25, marker="s", linewidth=1.8, linestyle="--", markersize=5.5, color="#FF7F0E", label="Severe r2SCAN flip (>25 meV, %)", zorder=4)
    ax1r.set_ylabel("Actual r2SCAN Instability Flip Rate (%)", color="#B01C1C")
    ax1r.set_ylim(0, 50)
    for idx_i, (xi, y0, mae_v) in enumerate(zip(x, flip0, maes)):
        # 막대 상단과 겹치지 않도록 우축 좌표를 조절해 라벨 위치 선정
        dy_off = 1.6 if idx_i != 6 else 1.8
        ax1r.text(
            xi,
            y0 + dy_off,
            f"{y0:.1f}%",
            ha="center",
            va="bottom",
            fontsize=7.9,
            color="#9E1111",
            fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.12", facecolor="white", edgecolor="none", alpha=0.78),
            zorder=5,
        )

    # 범례 통합
    h1, lb1 = ax1.get_legend_handles_labels()
    h2, lb2 = ax1r.get_legend_handles_labels()
    ax1.legend(h1 + h2, lb1 + lb2, loc="upper left", frameon=True, framealpha=0.92, edgecolor="#DDDDDD", fontsize=8.2)
    ax1.text(
        0.02,
        0.68,
        f"Raw PBE-r2SCAN MAE: {t2['raw_mae_mev']:.2f} meV/atom\n"
        f"Elemental-shift R²: {100.0 * t2['variance_explained_by_ref_shift_r2']:.2f}%\n"
        f"Residual η MAE: {t2['residual_mae_mev']:.2f} meV (-{t2['mae_reduction_pct']:.2f}%)",
        transform=ax1.transAxes,
        fontsize=8.3,
        bbox=dict(boxstyle="round,pad=0.35", facecolor="#F7F9FC", edgecolor="#C5D2E3"),
    )

    # 패널 (b): Robust vs. Fragile 실제 r2SCAN 전복률 분리
    ex117 = gc["matched_117k_exact_hull_validation"]
    extp = gc["external_proxy_validation_decomp_energy"]
    gk = sa["gnome_oos_5fold_calibration"]["exact_charnes_cooper_lp_chemical_system_group_5fold"]
    gk_thresh = gk["oos_exact_lp_threshold_1x"]

    gk_rob = gk_thresh["robust_flip_gt0_pct"]
    gk_frag = gk_thresh["fragile_flip_gt0_pct"]
    gk_rr = gk_thresh["relative_risk_gt0"]

    regimes = [
        "LP Unif.\n10 meV",
        "LP Unif.\n25 meV",
        "LP Unif.\n50 meV",
        "LP Lit.\nHetero",
        "GroupKFold\nOOS LP",
        "Ext. Proxy\nLit. Het.",
    ]
    rob_rates = [
        ex117["flip_gt0_by_10mev"]["low_risk_flip_rate_pct"],
        ex117["flip_gt0_by_25mev"]["low_risk_flip_rate_pct"],
        ex117["flip_gt0_by_50mev"]["low_risk_flip_rate_pct"],
        ex117["flip_gt0_by_hetero"]["low_risk_flip_rate_pct"],
        gk_rob,
        extp["flip_gt0_by_hetero_proxy"]["low_risk_flip_rate_pct"],
    ]
    frag_rates = [
        ex117["flip_gt0_by_10mev"]["high_risk_flip_rate_pct"],
        ex117["flip_gt0_by_25mev"]["high_risk_flip_rate_pct"],
        ex117["flip_gt0_by_50mev"]["high_risk_flip_rate_pct"],
        ex117["flip_gt0_by_hetero"]["high_risk_flip_rate_pct"],
        gk_frag,
        extp["flip_gt0_by_hetero_proxy"]["high_risk_flip_rate_pct"],
    ]
    rr_vals = [
        ex117["flip_gt0_by_10mev"]["relative_risk_high_vs_low"],
        ex117["flip_gt0_by_25mev"]["relative_risk_high_vs_low"],
        ex117["flip_gt0_by_50mev"]["relative_risk_high_vs_low"],
        ex117["flip_gt0_by_hetero"]["relative_risk_high_vs_low"],
        gk_rr,
        extp["flip_gt0_by_hetero_proxy"]["relative_risk_high_vs_low"],
    ]

    x2 = np.arange(len(regimes))
    w = 0.36
    b_rob = ax2.bar(x2 - w / 2, rob_rates, width=w, color="#2CA02C", alpha=0.88, label="Certified Robust / Low-Risk", zorder=2)
    b_frag = ax2.bar(x2 + w / 2, frag_rates, width=w, color="#D62728", alpha=0.88, label="Certified Fragile / High-Risk", zorder=2)
    ax2.set_xticks(x2)
    ax2.set_xticklabels(regimes, fontsize=8.4)
    ax2.set_ylabel("Actual r2SCAN Flip Rate (%)")
    ax2.set_ylim(0, 22.8)
    ax2.grid(axis="y", linestyle="--", alpha=0.35, zorder=0)
    ax2.set_title("(b) Empirical r2SCAN Flip Stratification (Relative Risk)", pad=10)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, edgecolor="#DDDDDD", fontsize=8.4)

    for br, bf, rr, r_v, f_v in zip(b_rob, b_frag, rr_vals, rob_rates, frag_rates):
        ax2.text(br.get_x() + br.get_width() / 2, r_v + 0.35, f"{r_v:.2f}%", ha="center", va="bottom", fontsize=7.5, color="#1D6F1D", fontweight="bold")
        ax2.text(bf.get_x() + bf.get_width() / 2, f_v + 0.35, f"{f_v:.1f}%", ha="center", va="bottom", fontsize=7.6, color="#9E1A1A", fontweight="bold")
        cx = 0.5 * (br.get_x() + bf.get_x() + bf.get_width())
        ax2.text(
            cx,
            max(r_v, f_v) + 1.85,
            f"{rr:.1f}x",
            ha="center",
            va="bottom",
            fontsize=8.2,
            fontweight="bold",
            color="#222222",
            bbox=dict(boxstyle="round,pad=0.18", facecolor="#FFF3CD", edgecolor="#E6C200", linewidth=0.8),
        )

    fig.tight_layout(w_pad=2.4)
    _save_fig(fig, "fig1_gnome_theorem2_and_crossval")


def generate_fig2_jarvis_ehull_forensic() -> None:
    """Figure 2: JARVIS-DFT 3D 공개 ehull 이중 나눗셈 결함 실측 산점도 및 음성대조군."""
    jp = json.loads((RESULTS_DIR / "jarvis_phase_summary.json").read_text(encoding="utf-8"))
    forensic = jp["published_ehull_forensic_audit"]

    with open(ROOT_DIR / "data" / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)

    elem_o88: Dict[str, float] = {}
    for d in jdata:
        o88 = d.get("optb88vdw_total_energy")
        if not (isinstance(o88, (int, float)) and math.isfinite(o88)):
            continue
        try:
            cnt = parse_formula_counts(d["formula"])
        except Exception:
            continue
        if len(cnt) == 1 and float(next(iter(cnt.values()))) == 1.0:
            el = next(iter(cnt))
            if el not in elem_o88 or float(o88) < elem_o88[el]:
                elem_o88[el] = float(o88)

    xs: List[float] = []
    ys: List[float] = []
    by_jid: Dict[str, Tuple[float, float, str]] = {}
    for d in jdata:
        o88 = d.get("optb88vdw_total_energy")
        eh = d.get("ehull")
        if not (isinstance(o88, (int, float)) and isinstance(eh, (int, float)) and math.isfinite(o88) and math.isfinite(eh)):
            continue
        try:
            cnt = parse_formula_counts(d["formula"])
        except Exception:
            continue
        n_fu = float(sum(cnt.values()))
        if len(cnt) > 1 and n_fu > 1.0 and all(el in elem_o88 for el in cnt):
            e_elem = sum((float(c) / n_fu) * elem_o88[el] for el, c in cnt.items())
            pred = (float(o88) / n_fu) - e_elem
            xs.append(pred)
            ys.append(float(eh))
            by_jid[d["jid"]] = (pred, float(eh), d["formula"])

    x_arr = np.asarray(xs, dtype=np.float64)
    y_arr = np.asarray(ys, dtype=np.float64)
    mask = (x_arr >= -0.3) & (x_arr <= 7.5) & (y_arr >= -0.3) & (y_arr <= 7.5)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.0), gridspec_kw={"width_ratios": [1.15, 0.95]})

    hb = ax1.hexbin(x_arr[mask], y_arr[mask], gridsize=55, bins="log", cmap="viridis", mincnt=1, zorder=2)
    cb = fig.colorbar(hb, ax=ax1, pad=0.02)
    cb.set_label("log10(Crystal Count)")
    ax1.plot([0, 7.2], [0, 7.2], linestyle="--", color="#D62728", linewidth=1.8, label="Exact y = x (Double Division)", zorder=3)

    # 대표 안정 기저상태 4건 강조
    spot_ids = [
        ("JVASP-106708", (0.28, -0.45)),
        ("JVASP-15157", (-2.10, 0.10)),
        ("JVASP-13318", (0.32, -0.45)),
        ("JVASP-152492", (0.32, 0.28)),
    ]
    for jid, (dx, dy) in spot_ids:
        if jid in by_jid:
            px, py, fm = by_jid[jid]
            ax1.scatter([px], [py], marker="*", s=130, color="#FF2A2A", edgecolor="white", linewidth=0.8, zorder=5)
            ax1.annotate(
                f"{jid}\n({fm})",
                xy=(px, py),
                xytext=(px + dx, py + dy),
                fontsize=7.6,
                fontweight="bold",
                color="#7A0000",
                bbox=dict(boxstyle="round,pad=0.18", facecolor="white", edgecolor="#D62728", alpha=0.92),
                arrowprops=dict(arrowstyle="->", color="#D62728", lw=0.9),
                zorder=6,
            )

    ax1.set_xlim(-0.2, 7.2)
    ax1.set_ylim(-0.2, 7.2)
    ax1.set_xlabel("Predicted Double-Divided Defect: $(E_{\\mathrm{optB88}} / N_{\\mathrm{fu}}) - E_{\\mathrm{elem\\_hull}}$ (eV/atom)")
    ax1.set_ylabel("Published Figshare ehull (eV/atom)")
    ax1.set_title("(a) JARVIS-DFT 3D Published ehull vs. Double-Division Model (n=92,955)", pad=10)
    ax1.grid(linestyle="--", alpha=0.3, zorder=0)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92)

    # 패널 (b): 가설 vs 두 음성대조군 일치율
    h_div = forensic["hypothesis_div_nfu_fit"]
    h_nodiv = forensic["negative_control_no_div_nfu"]
    h_rand = forensic["negative_control_random_elem_refs"]

    models = [
        "Double-Division\nHypothesis\n(E/N_fu - E_elem)",
        "Neg. Control 1\n(No 1/N_fu\nDivision)",
        "Neg. Control 2\n(Permuted\nElem. Refs)",
    ]
    lt01 = [h_div["match_lt_0_01ev_pct"], h_nodiv["match_lt_0_01ev_pct"], h_rand["match_lt_0_01ev_pct"]]
    lt05 = [h_div["match_lt_0_05ev_pct"], h_nodiv["match_lt_0_05ev_pct"], h_rand["match_lt_0_05ev_pct"]]
    meds = [h_div["median_abs_residual_ev"], h_nodiv["median_abs_residual_ev"], h_rand["median_abs_residual_ev"]]

    xb = np.arange(len(models))
    wb = 0.34
    b1 = ax2.bar(xb - wb / 2, lt01, width=wb, color="#1F77B4", alpha=0.9, label="Match within < 0.01 eV/atom (%)", zorder=2)
    b2 = ax2.bar(xb + wb / 2, lt05, width=wb, color="#2CA02C", alpha=0.88, label="Match within < 0.05 eV/atom (%)", zorder=2)
    ax2.set_xticks(xb)
    ax2.set_xticklabels(models, fontsize=8.6)
    ax2.set_ylabel("Multinary Agreement Rate (%)")
    ax2.set_ylim(0, 106)
    ax2.grid(axis="y", linestyle="--", alpha=0.35, zorder=0)
    ax2.set_title("(b) Forensic Fit vs. Negative Controls (N=92,955)", pad=10)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=8.3)

    for r1, r2, v1, v2, md in zip(b1, b2, lt01, lt05, meds):
        ax2.text(r1.get_x() + r1.get_width() / 2, v1 + 1.5, f"{v1:.2f}%", ha="center", va="bottom", fontsize=8, fontweight="bold", color="#124E78")
        ax2.text(r2.get_x() + r2.get_width() / 2, v2 + 1.5, f"{v2:.2f}%", ha="center", va="bottom", fontsize=8, fontweight="bold", color="#196F19")
        cx = 0.5 * (r1.get_x() + r2.get_x() + r2.get_width())
        ax2.text(
            cx,
            max(v1, v2) + 8.5,
            f"Med. |res|\n{md:.4f} eV" if md < 0.1 else f"Med. |res|\n{md:.3f} eV",
            ha="center",
            va="bottom",
            fontsize=8,
            bbox=dict(boxstyle="round,pad=0.22", facecolor="#F4F6F9", edgecolor="#CCCCCC"),
        )

    fig.tight_layout(w_pad=2.4)
    _save_fig(fig, "fig2_jarvis_ehull_forensic")


def generate_fig3_jarvis_elastic_born_mandel() -> None:
    """Figure 3: JARVIS-DFT 3D 34,323개 6x6 탄성 텐서 Born·Mandel·Voigt·대칭성 전수 감사."""
    je = json.loads((RESULTS_DIR / "jarvis_elastic_summary.json").read_text(encoding="utf-8"))
    sa = json.loads((RESULTS_DIR / "supplementary_analysis.json").read_text(encoding="utf-8"))

    by_cs = je["by_crystal_system"]
    cs_order = sorted(by_cs.keys(), key=lambda k: by_cs[k]["total"])
    cs_labels = {
        "cubic": "Cubic",
        "hexagonal": "Hexagonal",
        "tetragonal_high": "Tetragonal (High)",
        "tetragonal_low": "Tetragonal (Low)",
        "trigonal_high": "Trigonal (High)",
        "trigonal_low": "Trigonal (Low)",
        "orthorhombic": "Orthorhombic",
        "monoclinic": "Monoclinic",
        "triclinic": "Triclinic",
    }

    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(15.4, 4.9), gridspec_kw={"width_ratios": [1.25, 0.95, 1.05]})

    # 패널 (a): 결정계별 Born & Mandel-10GPa 누적 막대
    y = np.arange(len(cs_order))
    m_rob10 = np.array([by_cs[k]["mandel_robust_10gpa"] for k in cs_order])
    pd_tot = np.array([by_cs[k]["born_pd"] for k in cs_order])
    m_frag10 = pd_tot - m_rob10
    non_pd = np.array([by_cs[k]["born_non_pd"] for k in cs_order])
    tot = np.array([by_cs[k]["total"] for k in cs_order])

    ax1.barh(y, m_rob10, color="#2CA02C", alpha=0.88, label="Born-PD & Mandel Robust (10 GPa)")
    ax1.barh(y, m_frag10, left=m_rob10, color="#FF7F0E", alpha=0.90, label="Born-PD & Mandel Fragile (<=10 GPa)")
    ax1.barh(y, non_pd, left=pd_tot, color="#D62728", alpha=0.85, label="Born Non-PD (Unc. Strain Witness)")
    ax1.set_yticks(y)
    ax1.set_yticklabels([cs_labels[k] for k in cs_order], fontsize=8.6)
    ax1.set_xlabel("Number of Crystals (JARVIS-DFT 3D)")
    ax1.set_xlim(0, 15200)
    ax1.grid(axis="x", linestyle="--", alpha=0.35)
    ax1.set_title("(a) Born & Mandel Stability by Crystal System", pad=10)
    ax1.legend(loc="lower right", frameon=True, framealpha=0.93, fontsize=7.8)

    for yi, t_val, npd_val in zip(y, tot, non_pd):
        pct = 100.0 * npd_val / t_val
        ax1.text(t_val + 160, yi, f"{t_val:,} ({pct:.1f}% non-PD)", va="center", ha="left", fontsize=7.8, color="#333333")

    # 패널 (b): Born-PD 22,842개에서 Voigt vs. SO(3)-Invariant Mandel 취약률
    tiers = np.array([1, 5, 10])
    voigt_pcts = [
        je["fragile_voigt_1gpa_among_pd_pct"],
        je["fragile_voigt_5gpa_among_pd_pct"],
        je["fragile_voigt_10gpa_among_pd_pct"],
    ]
    mandel_pcts = [
        100.0 * je["fragile_mandel_1gpa_among_pd"] / je["born_pd_count"],
        je["fragile_mandel_5gpa_among_pd_pct"],
        je["fragile_mandel_10gpa_among_pd_pct"],
    ]
    voigt_cnts = [je["fragile_voigt_1gpa_among_pd"], je["fragile_voigt_5gpa_among_pd"], je["fragile_voigt_10gpa_among_pd"]]
    mandel_cnts = [je["fragile_mandel_1gpa_among_pd"], je["fragile_mandel_5gpa_among_pd"], je["fragile_mandel_10gpa_among_pd"]]

    ax2.plot(tiers, voigt_pcts, marker="o", linewidth=2.2, markersize=6.5, color="#1F77B4", label="Unconstrained Voigt (WEYL_FRAGILE)")
    ax2.plot(tiers, mandel_pcts, marker="s", linewidth=2.2, markersize=6.5, color="#9467BD", label="SO(3)-Invariant Mandel (MANDEL_WEYL_FRAGILE)")
    ax2.fill_between(tiers, mandel_pcts, voigt_pcts, color="#1F77B4", alpha=0.10)
    for t_g, vp, mp, vc, mc in zip(tiers, voigt_pcts, mandel_pcts, voigt_cnts, mandel_cnts):
        if t_g == 1:
            ax2.text(t_g + 0.15, vp + 1.1, f"{vp:.2f}% ({vc:,})", ha="left", va="bottom", fontsize=7.8, color="#145388", fontweight="bold")
            ax2.text(t_g + 0.35, mp - 0.15, f"{mp:.2f}% ({mc:,})", ha="left", va="top", fontsize=7.8, color="#5C3A82", fontweight="bold")
        else:
            ax2.text(t_g, vp + 0.9, f"{vp:.2f}%\n({vc:,})", ha="center", va="bottom", fontsize=7.8, color="#145388", fontweight="bold")
            ax2.text(t_g, mp - 1.1, f"{mp:.2f}%\n({mc:,})", ha="center", va="top", fontsize=7.8, color="#5C3A82", fontweight="bold")
    ax2.set_xticks(tiers)
    ax2.set_xticklabels(["1 GPa", "5 GPa", "10 GPa"])
    ax2.set_xlabel("Perturbation Radius δ (GPa)")
    ax2.set_ylabel("Fragile Share Among 22,842 Born-PD Crystals (%)")
    ax2.set_ylim(0, 29.0)
    ax2.set_xlim(0.2, 11.4)
    ax2.grid(linestyle="--", alpha=0.35)
    ax2.set_title("(b) Bidirectional Weyl Fragility (Voigt vs. Mandel)", pad=10)
    ax2.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.7)

    # 패널 (c): 대칭성 위반 및 Non-PD 심각도 비교
    sv = je["symmetry_violations"]
    pd_s = sa["jarvis_elastic_deep"]["pd_symmetry_violations"]
    cat_labels = [
        "Matrix\nAsym.\n(>1 GPa)",
        "Symm.\nAxis-Perm\n(>1 GPa)",
        "Symm.\nFixed-Std\n(>1 GPa)",
        "Cubic\nMandel Deg.\n(>1 GPa)",
    ]
    all_viol_pct = [
        100.0 * sv["matrix_asym_gt_1gpa"] / je["n_valid_6x6"],
        100.0 * sv["voigt_any_gt_1gpa"] / je["n_valid_6x6"],
        100.0 * sv["voigt_fixed_std_gt_1gpa"] / je["n_valid_6x6"],
        100.0 * sv["cubic_mandel_rot_inv_gt_1gpa"] / by_cs["cubic"]["total"],
    ]
    pd_viol_pct = [
        100.0 * pd_s["pd_matrix_asym_gt_1gpa"] / je["born_pd_count"],
        pd_s["pd_voigt_any_gt_1gpa_pct"],
        100.0 * pd_s["pd_voigt_fixed_std_gt_1gpa"] / je["born_pd_count"],
        pd_s["pd_cubic_mandel_rot_gt_1gpa_pct"],
    ]

    xc = np.arange(len(cat_labels))
    wc = 0.36
    ba = ax3.bar(xc - wc / 2, all_viol_pct, width=wc, color="#8C564B", alpha=0.88, label="All Valid Tensors (N=34,323 / Cubic 9,096)")
    bp = ax3.bar(xc + wc / 2, pd_viol_pct, width=wc, color="#17BECF", alpha=0.88, label="Born-PD Subset (N=22,842 / Cubic 6,232)")
    ax3.set_xticks(xc)
    ax3.set_xticklabels(cat_labels, fontsize=8.0)
    ax3.set_ylabel("Violation Rate (%)")
    ax3.set_ylim(0, 21.5)
    ax3.grid(axis="y", linestyle="--", alpha=0.35)
    ax3.set_title("(c) Matrix & Crystal-Symmetry Audit", pad=10)
    ax3.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.8)

    for ra, rp, va, vp in zip(ba, bp, all_viol_pct, pd_viol_pct):
        ax3.text(ra.get_x() + ra.get_width() / 2, va + 0.35, f"{va:.2f}%", ha="center", va="bottom", fontsize=7.6, color="#5C362E", fontweight="bold")
        ax3.text(rp.get_x() + rp.get_width() / 2, vp + 0.35, f"{vp:.2f}%", ha="center", va="bottom", fontsize=7.6, color="#0D6E7A", fontweight="bold")

    fig.tight_layout(w_pad=2.0)
    _save_fig(fig, "fig3_jarvis_elastic_born_mandel")


def generate_fig4_wbm_collapse_and_phase_switching() -> None:
    """Figure 4: Matbench Discovery WBM 배치 붕괴 분해 및 4대 DB Phase Switching 비교."""
    wp = json.loads((RESULTS_DIR / "wbm_phase_summary.json").read_text(encoding="utf-8"))
    jp = json.loads((RESULTS_DIR / "jarvis_phase_summary.json").read_text(encoding="utf-8"))
    gp = json.loads((RESULTS_DIR / "gnome_pbe_full_summary.json").read_text(encoding="utf-8"))
    gr = json.loads((RESULTS_DIR / "gnome_r2scan_full_summary.json").read_text(encoding="utf-8"))

    sub = wp["mp2020_reported_stable_subset"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.4, 5.0), gridspec_kw={"width_ratios": [0.95, 1.15]})

    # 패널 (a): WBM 정적 MP2020 안정상(42,688 / 고유 프로토타입 32,805) 내부 붕괴 분해
    groups = ["All MP2020-Stable\n(N = 42,688)", "Unique-Prototype\nSubset (N = 32,805)"]
    poly = np.array([sub["unstable_by_same_composition_polymorph"], sub["unique_prototype_unstable_same_polymorph"]])
    cross = np.array([sub["unstable_by_cross_composition_decomp"], sub["unique_prototype_unstable_cross_composition"]])
    tot_n = np.array([sub["n_mp2020_ehull_le_0"], sub["unique_prototype_mp2020_stable_count"]])
    rem = tot_n - poly - cross

    poly_pct = 100.0 * poly / tot_n
    cross_pct = 100.0 * cross / tot_n
    rem_pct = 100.0 * rem / tot_n

    x1 = np.arange(len(groups))
    w1 = 0.48
    ax1.bar(x1, poly_pct, width=w1, color="#D62728", alpha=0.88, label="Collapse: Same-Composition Polymorph")
    ax1.bar(x1, cross_pct, bottom=poly_pct, width=w1, color="#FF7F0E", alpha=0.90, label="Collapse: Cross-Composition Decomposition")
    ax1.bar(x1, rem_pct, bottom=poly_pct + cross_pct, width=w1, color="#2CA02C", alpha=0.85, label="Remains Stable on Intra-WBM Hull")

    for xi, p_v, c_v, r_v, p_n, c_n, r_n in zip(x1, poly_pct, cross_pct, rem_pct, poly, cross, rem):
        ax1.text(xi, p_v / 2, f"{p_v:.1f}%\n({p_n:,})", ha="center", va="center", color="white", fontsize=8.5, fontweight="bold")
        ax1.text(xi, p_v + c_v / 2, f"{c_v:.1f}%\n({c_n:,})", ha="center", va="center", color="white", fontsize=8.5, fontweight="bold")
        ax1.text(xi, p_v + c_v + r_v / 2, f"{r_v:.1f}%\n({r_n:,})", ha="center", va="center", color="white", fontsize=8.5, fontweight="bold")
        ax1.text(
            xi,
            p_v + c_v + 1.0,
            f"Total Collapsed: {p_v + c_v:.2f}%",
            ha="center",
            va="bottom",
            fontsize=8.2,
            fontweight="bold",
            color="#7A0000",
            bbox=dict(boxstyle="round,pad=0.18", facecolor="white", edgecolor="#D62728", alpha=0.92),
        )

    ax1.set_xticks(x1)
    ax1.set_xticklabels(groups, fontsize=9.0)
    ax1.set_ylabel("Share of Static-MP2020-Stable Candidates (%)")
    ax1.set_ylim(0, 118)
    ax1.grid(axis="y", linestyle="--", alpha=0.35)
    ax1.set_title("(a) WBM Batch-Discovery Hull Collapse Breakdown", pad=10)
    ax1.legend(loc="upper center", frameon=True, framealpha=0.94, fontsize=8.0, ncol=1)

    # 패널 (b): 4대 DB Fragile 비율 + Phase Switching
    dbs = [
        ("JARVIS-DFT 3D\n(OptB88vdW)", jp),
        ("Matbench WBM\n(MP2020)", wp),
        ("GNoME r2SCAN\n(Intra-Hull)", gr),
        ("GNoME PBE\n(Intra-Hull)", gp),
    ]
    f10, f25, f50, fhet, ps_pct, ps_max = [], [], [], [], [], []
    for _, sm in dbs:
        ns = sm["n_nom_stable"]
        f10.append(100.0 * sm["nom_stable_status_10mev"]["Fragile"] / ns)
        f25.append(100.0 * sm["nom_stable_status_25mev"]["Fragile"] / ns)
        f50.append(100.0 * sm["nom_stable_status_50mev"]["Fragile"] / ns)
        fhet.append(100.0 * sm["nom_stable_status_hetero"]["Fragile"] / ns)
        ps_pct.append(sm["phase_switching"]["nom_stable_pct"])
        ps_max.append(sm["phase_switching"]["nom_stable_overest_max_pct"])

    x2 = np.arange(len(dbs))
    wb = 0.19
    b10 = ax2.bar(x2 - 1.5 * wb, f10, width=wb, color="#A6CEE3", label="Uniform 10 meV")
    b25 = ax2.bar(x2 - 0.5 * wb, f25, width=wb, color="#1F78B4", label="Uniform 25 meV")
    b50 = ax2.bar(x2 + 0.5 * wb, f50, width=wb, color="#08306B", label="Uniform 50 meV")
    bhet = ax2.bar(x2 + 1.5 * wb, fhet, width=wb, color="#E31A1C", alpha=0.88, label="Heterogeneous Profile")

    for xi, v10, v25, v50, vhet, psp, psm in zip(x2, f10, f25, f50, fhet, ps_pct, ps_max):
        ax2.text(xi - 1.5 * wb, v10 + 1.0, f"{v10:.0f}%", ha="center", va="bottom", fontsize=7.2)
        ax2.text(xi - 0.5 * wb, v25 + 1.0, f"{v25:.0f}%", ha="center", va="bottom", fontsize=7.2)
        ax2.text(xi + 0.5 * wb, v50 + 1.0, f"{v50:.0f}%", ha="center", va="bottom", fontsize=7.2)
        ax2.text(xi + 1.5 * wb, vhet + 1.0, f"{vhet:.0f}%", ha="center", va="bottom", fontsize=7.2, fontweight="bold", color="#99000D")
        ax2.text(
            xi,
            max(v50, vhet) + 7.5,
            f"Switching: {psp:.2f}%\n(Max +{psm:.1f}%)",
            ha="center",
            va="bottom",
            fontsize=7.6,
            bbox=dict(boxstyle="round,pad=0.2", facecolor="#FFF8E7", edgecolor="#D99B00", lw=0.8),
        )

    ax2.set_xticks(x2)
    ax2.set_xticklabels([d[0] for d in dbs], fontsize=8.6)
    ax2.set_ylabel("Fragile Share of Nominally Stable Phases (%)")
    ax2.set_ylim(0, 112)
    ax2.grid(axis="y", linestyle="--", alpha=0.35)
    ax2.set_title("(b) Multi-Tier Fragility & Phase Switching Across 4 Databases", pad=10)
    ax2.legend(loc="upper right", ncol=2, frameon=True, framealpha=0.93, fontsize=7.9)

    fig.tight_layout(w_pad=2.2)
    _save_fig(fig, "fig4_wbm_collapse_and_phase_switching")


def generate_fig5_certmat_architecture() -> None:
    """Figure 5: CertMat 아키텍처 및 Lean 4 Trusted Computing Base (TCB) 경계 도식."""
    fig, ax = plt.subplots(figsize=(13.6, 4.7))
    ax.set_xlim(0, 100)
    ax.set_ylim(0, 36)
    ax.axis("off")

    # 상단 제목
    ax.text(
        50,
        34.2,
        "CertMat Verification Architecture: Decoupled Search, Exact Rational Synthesis & Lean 4 TCB",
        ha="center",
        va="center",
        fontsize=12.2,
        fontweight="bold",
        color="#1A2433",
    )

    # TCB 외곽 배경 구분 박스
    out_tcb = FancyBboxPatch((21.5, 4.0), 37.5, 27.5, boxstyle="round,pad=0.5,rounding_size=1.2", facecolor="#F8FAFC", edgecolor="#94A3B8", linestyle="--", linewidth=1.3, zorder=1)
    in_tcb = FancyBboxPatch((61.0, 4.0), 17.5, 27.5, boxstyle="round,pad=0.5,rounding_size=1.2", facecolor="#ECFDF5", edgecolor="#047857", linewidth=2.2, zorder=1)
    ax.add_patch(out_tcb)
    ax.add_patch(in_tcb)
    ax.text(40.25, 30.1, "OUTSIDE TCB (Untrusted Witness Generation)", ha="center", va="center", fontsize=8.6, fontweight="bold", color="#475569")
    ax.text(69.75, 30.1, "LEAN 4 TCB", ha="center", va="center", fontsize=9.0, fontweight="bold", color="#065F46")

    def _box(x: float, y: float, w: float, h: float, title: str, body: str, fc: str, ec: str, tc: str = "#111827") -> None:
        p = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.35,rounding_size=0.9", facecolor=fc, edgecolor=ec, linewidth=1.6, zorder=3)
        ax.add_patch(p)
        ax.text(x + w / 2, y + h - 2.6, title, ha="center", va="center", fontsize=9.2, fontweight="bold", color=tc, zorder=4)
        ax.text(x + w / 2, y + (h - 3.6) / 2, body, ha="center", va="center", fontsize=7.9, color="#1F2937", linespacing=1.32, zorder=4)

    # 5개 아키텍처 블록
    _box(
        1.5,
        6.5,
        17.5,
        21.0,
        "1. Public Benchmarks",
        "SHA-256 Hard-Pinned\n\n"
        "- GNoME PBE (554,054)\n"
        "- GNoME r2SCAN (139,541)\n"
        "- GNoME 1:1 (117,043 x 2)\n"
        "- JARVIS-DFT (93,902)\n"
        "- JARVIS Elastic (34,323)\n"
        "- Matbench WBM (256,963)",
        "#EFF6FF",
        "#2563EB",
        "#1E3A8A",
    )

    _box(
        23.0,
        6.5,
        15.5,
        21.0,
        "2. Fast Screening",
        "Floating-Point Search\n\n"
        "- HiGHS Simplex Basis\n"
        "- 2-Polymorph Pruning\n"
        "- Charnes-Cooper LP\n"
        "- Eigen / Symmetry Pre-scan\n"
        "(Zero Trust Placed\n"
        "on Floats)",
        "#FFF7ED",
        "#EA580C",
        "#9A3412",
    )

    _box(
        41.0,
        6.5,
        16.5,
        21.0,
        "3. Exact Rational Core",
        "Exact Q & Z3 SMT\n\n"
        "- Fraction Gauss-Jordan\n"
        "- Z3 SMT Tie Fallback\n"
        "  (1.37% of LPs)\n"
        "- Exact LDL^T + Rank-1\n"
        "- Emit 12 Rational\n"
        "  Certificate Types",
        "#FEFCE8",
        "#CA8A04",
        "#854D0E",
    )

    _box(
        62.2,
        6.5,
        15.1,
        21.0,
        "4. certmat-check",
        "Lean 4 v4.16.0 Kernel\n\n"
        "- 51 Core Theorems\n"
        "- 0 Mathlib / 0 sorry\n"
        "- Standard Axioms Only\n"
        "- Farkas / RefCancel /\n"
        "  IntervalHull / Born\n"
        "  Voigt + Mandel Weyl",
        "#D1FAE5",
        "#059669",
        "#064E3B",
    )

    _box(
        80.5,
        6.5,
        18.0,
        21.0,
        "5. Certified Audit",
        "100% Machine Verified\n\n"
        "- 95,348 / 95,348 TSV\n"
        "  Lean + Fraction Parity\n"
        "- 540 / 540 Raw-DB\n"
        "  Full-Vector Binding\n"
        "- 15 / 15 Pytest Suites\n"
        "- 49-File SHA-256 Lock",
        "#F3E8FF",
        "#7C3AED",
        "#4C1D95",
    )

    # 화살표 연결
    arrow_kw = dict(arrowstyle="-|>,head_width=0.45,head_length=0.65", lw=1.8, color="#334155", zorder=5)
    for x0, x1 in ((19.2, 22.8), (38.7, 40.8), (57.7, 62.0), (77.5, 80.3)):
        ax.annotate("", xy=(x1, 17.0), xytext=(x0, 17.0), arrowprops=arrow_kw)

    # 하단 요약 캡션 바
    ax.text(
        50,
        1.5,
        "Total Audited: 1,312,869 Stability Evaluations (1,278,545 Competed LPs + 1 Uncompeted + 34,323 Elastic Tensors) | Fail-Closed Reproducibility via `reproduce_all.py`",
        ha="center",
        va="center",
        fontsize=8.4,
        color="#334155",
        style="italic",
    )

    _save_fig(fig, "fig5_certmat_architecture")


def main() -> None:
    """5개 논문 Figure를 순차 생성한다."""
    generate_fig1_gnome_theorem2_and_crossval()
    generate_fig2_jarvis_ehull_forensic()
    generate_fig3_jarvis_elastic_born_mandel()
    generate_fig4_wbm_collapse_and_phase_switching()
    generate_fig5_certmat_architecture()


if __name__ == "__main__":
    main()
