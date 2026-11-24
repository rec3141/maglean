#!/usr/bin/env python3
"""End-to-end verification tests for the compiled native `maglean` CLI and converter."""

import hashlib
import json
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin" / "maglean"
CONVERTER = ROOT / "scripts" / "convert_evidence.py"
EXAMPLES = ROOT / "examples"
REGRESSION = ROOT / "Tests" / "regression"
REAL_FIXTURES = EXAMPLES / "real_tool_outputs"


def run_cli(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(BIN), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def run_converter(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(CONVERTER), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def parse_frac(s: str) -> Fraction:
    return Fraction(s)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_hq_ecoli():
    path = EXAMPLES / "hq_ecoli_mag.json"
    res = run_cli("--json", str(path))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["mag_id"] == "MAG_001_Ecoli_HQ"
    assert data["input_sha256"] == file_sha256(path)
    assert data["maglean_version"] == "0.2.0"
    assert len(data["git_commit"]) >= 7
    assert "4.36.0" in data["lean_toolchain"]
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert parse_frac(data["marker_mass_exact"]) == Fraction(1)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
    assert data["accessory_contigs"] == 1
    assert data["accessory_bp"] == 95000
    assert data["marker_bearing_contigs"] == 3
    for ra in data["rank_audits"]:
        assert parse_frac(ra["purity_cons"]) == Fraction(1)
        assert parse_frac(ra["chimerism"]) == Fraction(0)
    print("PASS: test_hq_ecoli")


def test_stealth_chimera():
    path = EXAMPLES / "stealth_chimera_mag.json"
    res = run_cli("--json", str(path))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["input_sha256"] == file_sha256(path)
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
    assert data["tax_coherent"] is True
    phylum = next(r for r in data["rank_audits"] if r["rank"] == "phylum")
    assert parse_frac(phylum["purity_cons"]) == Fraction(1, 2)
    assert parse_frac(phylum["chimerism"]) == Fraction(1, 2)
    assert any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"])
    print("PASS: test_stealth_chimera")


def test_unclassified_dilution():
    res = run_cli("--json", str(EXAMPLES / "unclassified_dilution_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert data["tax_coherent"] is True
    phylum = next(r for r in data["rank_audits"] if r["rank"] == "phylum")
    genus = next(r for r in data["rank_audits"] if r["rank"] == "genus")
    assert parse_frac(phylum["purity_drop"]) == Fraction(1, 2)
    assert parse_frac(genus["purity_drop"]) == Fraction(1)
    assert parse_frac(genus["purity_cons"]) == Fraction(1, 2)
    assert parse_frac(genus["purity_opt"]) == Fraction(1)
    assert parse_frac(genus["unclassified_frac"]) == Fraction(1, 2)
    assert any("UNCLASSIFIED_DILUTION_ALERT" in a for a in data["alerts"])
    print("PASS: test_unclassified_dilution")


def test_patescibacteria_reduced():
    res = run_cli("--json", str(EXAMPLES / "patescibacteria_reduced_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert parse_frac(data["completeness_exact"]) == Fraction(7, 10)
    assert parse_frac(data["contamination_exact"]) == Fraction(0)
    assert data["mimag_tier"] == "Medium-Quality (MIMAG MQ)"
    assert data["tax_coherent"] is True
    assert parse_frac(data["completeness_exact"]) + parse_frac(data["contamination_exact"]) == parse_frac(data["marker_mass_exact"])
    print("PASS: test_patescibacteria_reduced")


def test_contaminated_mag():
    res = run_cli("--json", str(EXAMPLES / "contaminated_mag.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert parse_frac(data["completeness_exact"]) == Fraction(1)
    assert parse_frac(data["contamination_exact"]) == Fraction(3, 10)
    assert parse_frac(data["marker_mass_exact"]) == Fraction(13, 10)
    assert parse_frac(data["composite_q5_exact"]) == Fraction(1) - 5 * Fraction(3, 10)
    assert parse_frac(data["strain_heterogeneity_exact"]) == Fraction(1, 4)
    assert data["mimag_tier"] == "Contaminated (Failed MIMAG <10% Cont)"
    cons_vals = [parse_frac(r["purity_cons"]) for r in data["rank_audits"]]
    assert cons_vals == sorted(cons_vals, reverse=True), f"Non-monotone purityCons: {cons_vals}"
    print("PASS: test_contaminated_mag")


def test_text_reports_provenance_and_ci_flag():
    hq = EXAMPLES / "hq_ecoli_mag.json"
    sc = EXAMPLES / "stealth_chimera_mag.json"
    res = run_cli(str(hq), str(sc))
    assert res.returncode == 0, res.stderr
    assert "MAG_001_Ecoli_HQ" in res.stdout
    assert "MAG_002_Stealth_Chimera" in res.stdout
    assert "STEALTH_CHIMERA_ALERT" in res.stdout
    assert file_sha256(hq) in res.stdout
    assert file_sha256(sc) in res.stdout
    assert "omitted by default (pass --ci" in res.stdout
    assert "kCheckTaxCoherent_sound" in res.stdout

    res_ci = run_cli("--ci", str(hq))
    assert res_ci.returncode == 0, res_ci.stderr
    assert "conditional on independent marker-set detections" in res_ci.stdout

    bad = run_cli(str(EXAMPLES / "nonexistent.json"))
    assert bad.returncode == 2
    print("PASS: test_text_reports_provenance_and_ci_flag")


def test_unclassified_is_not_chimerism():
    res = run_cli("--json", str(REGRESSION / "unclassified_species_single_taxon.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"]), data["alerts"]
    print("PASS: test_unclassified_is_not_chimerism")


def test_sparse_rank_second_taxon_is_not_chimerism():
    res = run_cli("--json", str(REGRESSION / "sparse_rank_two_taxa.json"))
    assert res.returncode == 0, res.stderr
    data = json.loads(res.stdout)
    assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"]), data["alerts"]
    print("PASS: test_sparse_rank_second_taxon_is_not_chimerism")


def test_rejects_unknown_rank_key():
    res = run_cli("--json", str(REGRESSION / "capitalised_rank_keys.json"))
    assert res.returncode == 2, res.stdout
    assert "Unknown taxonomy rank" in res.stderr
    print("PASS: test_rejects_unknown_rank_key")


def test_rejects_duplicate_marker_sets():
    res = run_cli("--json", str(REGRESSION / "duplicate_marker_sets.json"))
    assert res.returncode == 2, res.stdout
    assert "duplicate marker sets" in res.stderr
    print("PASS: test_rejects_duplicate_marker_sets")


def test_rejects_zero_length_contig():
    res = run_cli("--json", str(REGRESSION / "zero_length_contig.json"))
    assert res.returncode == 2, res.stdout
    assert "contig length must be positive" in res.stderr
    print("PASS: test_rejects_zero_length_contig")


def test_converter_real_ecoli_mg1655():
    fx = REAL_FIXTURES / "ecoli_mg1655"
    with tempfile.TemporaryDirectory() as tmp:
        out_json = Path(tmp) / "ecoli_mg1655.json"
        conv = run_converter(
            "--mag-id", "GCF_000005845.2_Ecoli_MG1655",
            "--lineage", "d__Bacteria;p__Pseudomonadota;c__Gammaproteobacteria;o__Enterobacterales;f__Enterobacteriaceae;g__Escherichia;s__Escherichia coli",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--bin-id", "GCF_000005845.2",
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
            "-o", str(out_json),
        )
        assert conv.returncode == 0, conv.stderr
        ev = json.loads(out_json.read_text(encoding="utf-8"))
        # All 20 standard amino acids (fMet merged into Met, SeC ignored)
        assert ev["rna"]["distinct_tRNAs"] == 20
        assert ev["rna"]["has_23S"] and ev["rna"]["has_16S"] and ev["rna"]["has_5S"]

        res = run_cli("--json", str(out_json))
        assert res.returncode == 0, res.stderr
        data = json.loads(res.stdout)
        assert data["input_sha256"] == file_sha256(out_json)
        assert data["num_marker_sets"] == 56
        assert parse_frac(data["completeness_exact"]) == Fraction(1)
        assert parse_frac(data["contamination_exact"]) == Fraction(0)
        assert data["mimag_tier"] == "High-Quality (MIMAG HQ)"
        assert data["tax_coherent"] is True
        assert data["alerts"] == [], data["alerts"]
    print("PASS: test_converter_real_ecoli_mg1655")


def test_converter_real_uba_mag():
    fx = REAL_FIXTURES / "uba_mag"
    with tempfile.TemporaryDirectory() as tmp:
        out_json = Path(tmp) / "uba_mag.json"
        conv = run_converter(
            "--mag-id", "UBA10002_Phocaeicola_MAG",
            "--lineage", "d__Bacteria;p__Bacteroidota;c__Bacteroidia;o__Bacteroidales;f__Bacteroidaceae;g__Phocaeicola",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--bin-id", "UBA10002",
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
            "-o", str(out_json),
        )
        assert conv.returncode == 0, conv.stderr
        ev = json.loads(out_json.read_text(encoding="utf-8"))
        # 19 canonical amino acids (pseudo Val and Undet excluded)
        assert ev["rna"]["distinct_tRNAs"] == 19
        assert ev["rna"]["has_16S"] and ev["rna"]["has_23S"] and not ev["rna"]["has_5S"]

        res = run_cli("--json", str(out_json))
        assert res.returncode == 0, res.stderr
        data = json.loads(res.stdout)
        assert data["input_sha256"] == file_sha256(out_json)
        assert parse_frac(data["completeness_exact"]) == Fraction(52, 56)
        assert parse_frac(data["contamination_exact"]) == Fraction(1, 56)
        assert parse_frac(data["marker_mass_exact"]) == Fraction(53, 56)
        # >90% comp & <5% cont, but missing 5S rRNA => downgraded to MQ!
        assert data["mimag_tier"] == "Medium-Quality (MIMAG MQ)"
        assert any("MIMAG_HQ_RNA_DOWNGRADE" in a for a in data["alerts"])
        assert not any("STEALTH_CHIMERA_ALERT" in a for a in data["alerts"])
        assert data["accessory_contigs"] == 1
        assert data["accessory_bp"] == 62100
        assert data["marker_bearing_contigs"] == 5
        assert data["tax_coherent"] is True
    print("PASS: test_converter_real_uba_mag")


def test_converter_strict_rejections():
    fx = REAL_FIXTURES / "ecoli_mg1655"
    with tempfile.TemporaryDirectory() as tmp:
        # 1. Unknown rank prefix (k__Bacteria instead of d__Bacteria)
        bad_tax = Path(tmp) / "bad_tax.tsv"
        bad_tax.write_text("contig_id\tlineage\nNC_000913.3\tk__Bacteria\n", encoding="utf-8")
        res1 = run_converter(
            "--mag-id", "bad1",
            "--contigs", str(fx / "contigs.tsv"),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--taxonomy", str(bad_tax),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
        )
        assert res1.returncode == 2
        assert "unknown rank prefix" in res1.stderr

        # 2. Missing contig in taxonomy table
        extra_contigs = Path(tmp) / "extra_contigs.tsv"
        extra_contigs.write_text(
            "contig_id\tlength\nNC_000913.3\t4641652\nNC_EXTRA\t50000\n",
            encoding="utf-8",
        )
        res2 = run_converter(
            "--mag-id", "bad2",
            "--contigs", str(extra_contigs),
            "--marker-sets", str(REAL_FIXTURES / "bacterial_markers.tsv"),
            "--checkm-hits", str(fx / "checkm_marker_gene_stats.tsv"),
            "--taxonomy", str(fx / "contig_taxonomy.tsv"),
            "--barrnap", str(fx / "barrnap.gff"),
            "--trnascan", str(fx / "trnascan.tsv"),
        )
        assert res2.returncode == 2
        assert "missing from taxonomy table" in res2.stderr
    print("PASS: test_converter_strict_rejections")


def test_cami_alert_calibration():
    """Regression tests for Issues #8 and #9 (CAMI II marine benchmark false alarms)."""
    with tempfile.TemporaryDirectory() as tmp:
        # 1. Congeneric species split (Issue #8): 100% pure at genus, split 50/50 at species
        congeneric = {
            "mag_id": "CAMI_Psychrobacter_Congeneric",
            "lineage": "d__Bacteria;p__Pseudomonadota;g__Psychrobacter",
            "marker_sets": [["M1"], ["M2"], ["M3"], ["M4"], ["M5"]],
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {
                    "id": "c1", "length": 1500000, "markers": ["M1", "M2", "M3"],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Pseudomonadales",
                        "family": "Moraxellaceae", "genus": "Psychrobacter",
                        "species": "Psychrobacter arcticus",
                    },
                },
                {
                    "id": "c2", "length": 1500000, "markers": ["M4", "M5"],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Pseudomonadales",
                        "family": "Moraxellaceae", "genus": "Psychrobacter",
                        "species": "Psychrobacter cryohalolentis",
                    },
                },
            ],
        }
        p1 = Path(tmp) / "congeneric.json"
        p1.write_text(json.dumps(congeneric), encoding="utf-8")
        # Default (max-chimera-rank=genus): NO false STEALTH_CHIMERA_ALERT, species impurity still reported!
        r_def = run_cli("--json", str(p1))
        assert r_def.returncode == 0, r_def.stderr
        d_def = json.loads(r_def.stdout)
        assert not any("STEALTH_CHIMERA_ALERT" in a for a in d_def["alerts"]), d_def["alerts"]
        assert parse_frac(d_def["species_conservative_impurity_exact"]) == Fraction(1, 2)
        # Opting into --max-chimera-rank species fires the alert
        r_sp = run_cli("--json", "--max-chimera-rank", "species", str(p1))
        assert r_sp.returncode == 0, r_sp.stderr
        assert any("STEALTH_CHIMERA_ALERT" in a for a in json.loads(r_sp.stdout)["alerts"])

        # 2. Mostly-unclassified rank (Issue #8): 75% unclassified at phylum, 13% A + 12% B
        sparse = {
            "mag_id": "CAMI_Mostly_Unclassified",
            "lineage": "d__Bacteria",
            "marker_sets": [["M1"], ["M2"], ["M3"], ["M4"], ["M5"]],
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {"id": "u1", "length": 750000, "markers": ["M1", "M2", "M3"], "taxonomy": {"domain": "Bacteria"}},
                {"id": "a1", "length": 130000, "markers": ["M4"], "taxonomy": {"domain": "Bacteria", "phylum": "Pseudomonadota"}},
                {"id": "b1", "length": 120000, "markers": ["M5"], "taxonomy": {"domain": "Bacteria", "phylum": "Bacteroidota"}},
            ],
        }
        p2 = Path(tmp) / "sparse.json"
        p2.write_text(json.dumps(sparse), encoding="utf-8")
        # Only 25% classified at phylum (<50% default min_classified_frac) => NO false alarm
        r_sp2 = run_cli("--json", str(p2))
        assert r_sp2.returncode == 0, r_sp2.stderr
        assert not any("STEALTH_CHIMERA_ALERT" in a for a in json.loads(r_sp2.stdout)["alerts"])

        # 3. Clean-bin drop-purity upward drift (Issue #9): 94% at family -> 98% at genus
        drift = {
            "mag_id": "CAMI_Clean_Drift",
            "lineage": "d__Bacteria",
            "marker_sets": [["M1"], ["M2"], ["M3"], ["M4"], ["M5"]],
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {
                    "id": "main", "length": 940000, "markers": ["M1", "M2", "M3", "M4", "M5"],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Escherichia",
                    },
                },
                {
                    "id": "noise_unclass", "length": 40000, "markers": [],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Vibrionaceae",
                    },
                },
                {
                    "id": "noise_small", "length": 20000, "markers": [],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Vibrionaceae", "genus": "Vibrio",
                    },
                },
            ],
        }
        p3 = Path(tmp) / "drift.json"
        p3.write_text(json.dumps(drift), encoding="utf-8")
        r_dr = run_cli("--json", str(p3))
        assert r_dr.returncode == 0, r_dr.stderr
        d_dr = json.loads(r_dr.stdout)
        # Coarser family drop-purity is 94% (>=90%), so rising to 94/96 at genus is benign drift
        assert not any("UNCLASSIFIED_DILUTION_ALERT" in a for a in d_dr["alerts"]), d_dr["alerts"]
    print("PASS: test_cami_alert_calibration")


def test_dilution_alert_small_denominator_gates():
    """Regression tests for Issue #14: both small-denominator dilution fixtures."""
    with tempfile.TemporaryDirectory() as tmp:
        # Fixture 1: 3.99 Mb family-only + 5 kb E. coli (species) + 5 kb Salmonella (genus)
        # Classified bp is 0.25% at genus and 0.125% at species => must NOT fire dilution alert.
        markers_60 = [[f"PF{i:05d}"] for i in range(1, 61)]
        f1 = {
            "mag_id": "Issue14_Tiny_Genus_And_Species",
            "lineage": "d__Bacteria",
            "marker_sets": markers_60,
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {
                    "id": "main", "length": 3990000, "markers": [f"PF{i:05d}" for i in range(1, 61)],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae",
                    },
                },
                {
                    "id": "ecoli_5k", "length": 5000, "markers": [],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Escherichia",
                        "species": "Escherichia coli",
                    },
                },
                {
                    "id": "salm_5k", "length": 5000, "markers": [],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Salmonella",
                    },
                },
            ],
        }
        p1 = Path(tmp) / "issue14_1.json"
        p1.write_text(json.dumps(f1), encoding="utf-8")
        r1 = run_cli("--json", str(p1))
        assert r1.returncode == 0, r1.stderr
        d1 = json.loads(r1.stdout)
        assert not any("UNCLASSIFIED_DILUTION_ALERT" in a for a in d1["alerts"]), d1["alerts"]

        # Fixture 2: genus passes coverage gate (100% classified, 50/50 split across two genera),
        # but only one tiny 5 kb contig reaches species (0.25% classified at species) => must NOT fire!
        f2 = {
            "mag_id": "Issue14_Genus_Covered_Species_Tiny",
            "lineage": "d__Bacteria",
            "marker_sets": markers_60,
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {
                    "id": "g1_big", "length": 995000, "markers": [f"PF{i:05d}" for i in range(1, 31)],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Escherichia",
                    },
                },
                {
                    "id": "g1_tiny_sp", "length": 5000, "markers": [],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Escherichia",
                        "species": "Escherichia coli",
                    },
                },
                {
                    "id": "g2_big", "length": 1000000, "markers": [f"PF{i:05d}" for i in range(31, 61)],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Salmonella",
                    },
                },
            ],
        }
        p2 = Path(tmp) / "issue14_2.json"
        p2.write_text(json.dumps(f2), encoding="utf-8")
        r2 = run_cli("--json", str(p2))
        assert r2.returncode == 0, r2.stderr
        d2 = json.loads(r2.stdout)
        assert not any("UNCLASSIFIED_DILUTION_ALERT" in a for a in d2["alerts"]), d2["alerts"]
    print("PASS: test_dilution_alert_small_denominator_gates")


def test_no_contig_radius_on_fragmentation():
    """Regression test for Issue #13: paired 1-contig vs 60-contig identical 4 Mb genome."""
    with tempfile.TemporaryDirectory() as tmp:
        markers_60 = [[f"PF{i:05d}"] for i in range(1, 61)]
        tax = {
            "domain": "Bacteria", "phylum": "Pseudomonadota",
            "class": "Gammaproteobacteria", "order": "Enterobacterales",
            "family": "Enterobacteriaceae", "genus": "Escherichia",
            "species": "Escherichia coli",
        }
        one = {
            "mag_id": "Frag_1_Contig", "lineage": "d__Bacteria",
            "marker_sets": markers_60,
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [{"id": "c1", "length": 4000000, "markers": [f"PF{i:05d}" for i in range(1, 61)], "taxonomy": tax}],
        }
        sixty = {
            "mag_id": "Frag_60_Contigs", "lineage": "d__Bacteria",
            "marker_sets": markers_60,
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {"id": f"c{i}", "length": 66666, "markers": [f"PF{i:05d}"], "taxonomy": tax}
                for i in range(1, 61)
            ],
        }
        p1, p60 = Path(tmp) / "one.json", Path(tmp) / "sixty.json"
        p1.write_text(json.dumps(one), encoding="utf-8")
        p60.write_text(json.dumps(sixty), encoding="utf-8")
        for p in (p1, p60):
            rt = run_cli(str(p))
            assert rt.returncode == 0, rt.stderr
            assert "Contig-Level Rad." not in rt.stdout
            rj = run_cli("--json", str(p))
            dj = json.loads(rj.stdout)
            assert "contig_hoeffding_95_radius_exact" not in dj
    print("PASS: test_no_contig_radius_on_fragmentation")


def test_purity_gated_verdict_on_yeast_chimera():
    """Regression test for Issue #15: E. coli + Cryptococcus chimera (HQ markers, 20.9% foreign bp)."""
    with tempfile.TemporaryDirectory() as tmp:
        markers = [[f"PF{i:05d}"] for i in range(1, 21)]
        chim = {
            "mag_id": "Zymo_Ecoli_Plus_Cryptococcus",
            "lineage": "d__Bacteria;g__Escherichia",
            "marker_sets": markers,
            "rna": {"has_23S": True, "has_16S": True, "has_5S": True, "distinct_tRNAs": 20},
            "contigs": [
                {
                    "id": "ecoli_chr", "length": 4750000, "markers": [f"PF{i:05d}" for i in range(1, 20)],
                    "taxonomy": {
                        "domain": "Bacteria", "phylum": "Pseudomonadota",
                        "class": "Gammaproteobacteria", "order": "Enterobacterales",
                        "family": "Enterobacteriaceae", "genus": "Escherichia",
                        "species": "Escherichia coli",
                    },
                },
                {
                    "id": "yeast_c1", "length": 1260000, "markers": [],
                    "taxonomy": {
                        "domain": "Eukaryota", "phylum": "Basidiomycota",
                        "class": "Tremellomycetes", "order": "Tremellales",
                        "family": "Cryptococcaceae", "genus": "Cryptococcus",
                        "species": "Cryptococcus neoformans",
                    },
                },
            ],
        }
        p = Path(tmp) / "yeast_chim.json"
        p.write_text(json.dumps(chim), encoding="utf-8")
        rj = run_cli("--json", str(p))
        assert rj.returncode == 0, rj.stderr
        dj = json.loads(rj.stdout)
        assert dj["mimag_tier"] == "High-Quality (MIMAG HQ)"
        assert dj["stealth_chimera_alert"] is True
        assert dj["purity_gate_passed"] is False
        assert dj["purity_gated_q5_exact"] is None
        rt = run_cli(str(p))
        assert "[WARNING: STEALTH_CHIMERA_ALERT" in rt.stdout
        assert "Purity-Gated Q_5   : REJECTED" in rt.stdout
    print("PASS: test_purity_gated_verdict_on_yeast_chimera")


def test_converter_merged_orfs_and_format_fixes():
    """Regression tests for Issues #11 and #12."""
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        (t / "contigs.tsv").write_text("contig_id\tlength\ncontig_001\t2000000\n", encoding="utf-8")
        (t / "markers.tsv").write_text("PF00177\nPF00297\n", encoding="utf-8")
        # Merged adjacent ORF key with TWO intervals for PF00177 (Issue #11 + #12.1)
        # plus an extra contig_999 for --filter-to-bin testing (Issue #12.6)
        (t / "checkm.tsv").write_text(
            "bin1\t{'contig_001_7202&&contig_001_7203': {'PF00177': [[1, 80], [120, 200]]}, "
            "'contig_001_10': {'PF00297': [[5, 95]]}, "
            "'contig_999_1': {'PF00297': [[1, 50]]}}\n",
            encoding="utf-8",
        )
        (t / "tax.tsv").write_text(
            "contig_id\tlineage\n"
            "contig_001\td__Bacteria;p__Pseudomonadota;g__Escherichia\n"
            "contig_999\td__Bacteria;p__Bacillota\n",
            encoding="utf-8",
        )
        # Barrnap GFF with eukaryotic 28S/18S/5_8S/12S (Issue #12.2), partial 16S (Issue #12.3),
        # complete 23S and 5S, plus extra contig_999
        (t / "barrnap.gff").write_text(
            "##gff-version 3\n"
            "contig_001\tbarrnap:0.9\trRNA\t1\t500\t0\t+\t.\tName=16S_rRNA;product=16S ribosomal RNA (partial)\n"
            "contig_001\tbarrnap:0.9\trRNA\t600\t3500\t0\t+\t.\tName=23S_rRNA;product=23S ribosomal RNA\n"
            "contig_001\tbarrnap:0.9\trRNA\t3600\t3720\t0\t+\t.\tName=5S_rRNA;product=5S ribosomal RNA\n"
            "contig_001\tbarrnap:0.9\trRNA\t4000\t5800\t0\t+\t.\tName=18S_rRNA;product=18S ribosomal RNA\n"
            "contig_001\tbarrnap:0.9\trRNA\t6000\t9000\t0\t+\t.\tName=28S_rRNA;product=28S ribosomal RNA\n"
            "contig_001\tbarrnap:0.9\trRNA\t9100\t9250\t0\t+\t.\tName=5_8S_rRNA;product=5.8S ribosomal RNA\n"
            "contig_001\tbarrnap:0.9\trRNA\t9300\t10200\t0\t+\t.\tName=12S_rRNA;product=12S ribosomal RNA\n"
            "contig_999\tbarrnap:0.9\trRNA\t1\t1500\t0\t+\t.\tName=16S_rRNA;product=16S ribosomal RNA\n",
            encoding="utf-8",
        )
        # tRNAscan-SE 12-column -H/--detail layout with pseudo in col 12 (Issue #12.4)
        # and SeC(p)/SeC(e) (Issue #12.5)
        (t / "trnascan.tsv").write_text(
            "Sequence\ttRNA #\tBegin\tEnd\ttRNA Type\tAnti Codon\tIntron Begin\tIntron End\tInf Score\tHMM\t2Str\tNote\n"
            "contig_001\t1\t10\t85\tAla\tTGC\t0\t0\t80.0\t70.0\t10.0\t\n"
            "contig_001\t2\t100\t175\tGly\tGCC\t0\t0\t30.0\t20.0\t10.0\tpseudo\n"
            "contig_001\t3\t200\t290\tSeC(p)\tTCA\t0\t0\t55.0\t45.0\t10.0\t\n"
            "contig_001\t4\t300\t390\tSeC(e)\tTCA\t0\t0\t54.0\t44.0\t10.0\t\n"
            "contig_999\t1\t10\t85\tVal\tTAC\t0\t0\t80.0\t70.0\t10.0\t\n",
            encoding="utf-8",
        )
        out = t / "out.json"
        # Without --filter-to-bin, extra contig_999 must be strictly rejected
        strict = run_converter(
            "--mag-id", "test", "--contigs", str(t / "contigs.tsv"),
            "--marker-sets", str(t / "markers.tsv"), "--checkm-hits", str(t / "checkm.tsv"),
            "--taxonomy", str(t / "tax.tsv"), "--barrnap", str(t / "barrnap.gff"),
            "--trnascan", str(t / "trnascan.tsv"), "-o", str(out),
        )
        assert strict.returncode == 2

        # With --filter-to-bin, conversion succeeds cleanly
        ok = run_converter(
            "--filter-to-bin",
            "--mag-id", "test_merged", "--contigs", str(t / "contigs.tsv"),
            "--marker-sets", str(t / "markers.tsv"), "--checkm-hits", str(t / "checkm.tsv"),
            "--taxonomy", str(t / "tax.tsv"), "--barrnap", str(t / "barrnap.gff"),
            "--trnascan", str(t / "trnascan.tsv"), "-o", str(out),
        )
        assert ok.returncode == 0, ok.stderr
        ev = json.loads(out.read_text(encoding="utf-8"))
        # Merged ORF with 2 intervals => exactly 2 copies of PF00177 + 1 copy of PF00297!
        assert ev["contigs"][0]["markers"].count("PF00177") == 2
        assert ev["contigs"][0]["markers"].count("PF00297") == 1
        # Partial 16S excluded; 23S & 5S present; 12-col pseudo Gly excluded; SeC(p)/SeC(e) ignored => 1 AA (Ala)
        assert ev["rna"]["has_16S"] is False
        assert ev["rna"]["has_23S"] is True
        assert ev["rna"]["has_5S"] is True
        assert ev["rna"]["distinct_tRNAs"] == 1

        # Verify MAGLean computes 100% completeness and 50% contamination (1 excess out of 2 sets)
        rj = run_cli("--json", str(out))
        assert rj.returncode == 0, rj.stderr
        dj = json.loads(rj.stdout)
        assert parse_frac(dj["completeness_exact"]) == Fraction(1)
        assert parse_frac(dj["contamination_exact"]) == Fraction(1, 2)

        # With --allow-partial-rrna, partial 16S is counted
        ok_p = run_converter(
            "--filter-to-bin", "--allow-partial-rrna",
            "--mag-id", "test_partial", "--contigs", str(t / "contigs.tsv"),
            "--marker-sets", str(t / "markers.tsv"), "--checkm-hits", str(t / "checkm.tsv"),
            "--taxonomy", str(t / "tax.tsv"), "--barrnap", str(t / "barrnap.gff"),
            "--trnascan", str(t / "trnascan.tsv"), "-o", str(out),
        )
        assert ok_p.returncode == 0, ok_p.stderr
        assert json.loads(out.read_text(encoding="utf-8"))["rna"]["has_16S"] is True

        # Cross-contig merged ORF key must be rejected!
        (t / "contigs2.tsv").write_text("contig_id\tlength\nc1\t1000\nc2\t1000\n", encoding="utf-8")
        (t / "bad_merge.tsv").write_text("bin1\t{'c1_1&&c2_2': {'PF00177': [[1, 50]]}}\n", encoding="utf-8")
        bad_m = run_converter(
            "--mag-id", "badm", "--contigs", str(t / "contigs2.tsv"),
            "--marker-sets", str(t / "markers.tsv"), "--checkm-hits", str(t / "bad_merge.tsv"),
            "--taxonomy", str(t / "tax.tsv"), "--barrnap", str(t / "barrnap.gff"),
            "--trnascan", str(t / "trnascan.tsv"),
        )
        assert bad_m.returncode == 2
        assert "spans multiple contigs" in bad_m.stderr
    print("PASS: test_converter_merged_orfs_and_format_fixes")


if __name__ == "__main__":
    if not BIN.exists():
        sys.exit(f"Binary not found: {BIN}")
    test_hq_ecoli()
    test_stealth_chimera()
    test_unclassified_dilution()
    test_patescibacteria_reduced()
    test_contaminated_mag()
    test_text_reports_provenance_and_ci_flag()
    test_unclassified_is_not_chimerism()
    test_sparse_rank_second_taxon_is_not_chimerism()
    test_rejects_unknown_rank_key()
    test_rejects_duplicate_marker_sets()
    test_rejects_zero_length_contig()
    test_converter_real_ecoli_mg1655()
    test_converter_real_uba_mag()
    test_converter_strict_rejections()
    test_cami_alert_calibration()
    test_dilution_alert_small_denominator_gates()
    test_no_contig_radius_on_fragmentation()
    test_purity_gated_verdict_on_yeast_chimera()
    test_converter_merged_orfs_and_format_fixes()
    print("\nALL 19 CLI, CAMI CALIBRATION, PROVENANCE & CONVERTER TESTS PASSED!")
