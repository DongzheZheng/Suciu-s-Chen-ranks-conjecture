#!/usr/bin/env python3
"""Check the release sources, build the project, and audit its theorem interface."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REVISION = "8a178386ffc0f5fef0b77738bb5449d50efeea95"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
AUDITS = [
    "checks/ActualChenRanksAFRSVersionOneAudit.lean",
    "checks/ActualCentralChenRanksAFRSVersionOneAudit.lean",
    "Verification.lean",
]
MAIN_THEOREMS = [
    "ChenRanks.AffineArrangement.chenRanks_affine",
    "ChenRanks.AffineArrangement.chenRanks_central",
]
EXPECTED_QUERIES = {
    AUDITS[0]: [
        "ChenRanks.Koszul.AFRSEffectiveCanonicalDecomposition",
        "ChenRanks.AffineArrangement.actualRationalChenRanks_paperRange_versionOne",
        "ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne",
        "ChenRanks.finiteChenRank_eq_rationalChenRank",
        "ChenRanks.AffineArrangement.actualRationalChenPiece_finiteDimensional",
        "ChenRanks.AffineArrangement.actualFiniteChenRank_eq_originalKoszulDegree",
        "ChenRanks.AffineArrangement.singularProjectiveComponentDimensionCount_eq_rational",
        "ChenRanks.AffineArrangement.actualResonanceChenRankExpression_eq_range",
        "ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression",
    ],
    AUDITS[1]: [
        "ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression",
        "ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne",
        "ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperSum_versionOne",
    ],
    AUDITS[2]: MAIN_THEOREMS,
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text):
    """Mask comments and strings while retaining code for a supplementary scan."""
    result = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            result.append(" ")
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
            result.append(" ")
        elif pair == "/-":
            depth = 1
            i += 2
            result.append(" ")
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            result.append(" ")
        elif text[i] == '"':
            string = True
            i += 1
            result.append(" ")
        else:
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment or string in Lean source")
    return "".join(result)


def check_sources():
    manifest_path = ROOT / "verification/SourceManifest.json"
    manifest = json.loads(manifest_path.read_text())
    for name, expected in manifest["files"].items():
        path = ROOT / name
        if not path.is_file() or sha256(path) != expected:
            raise ValueError("Release source hash mismatch: " + name)
    lean_files = {name for name in manifest["files"] if name.endswith(".lean")}
    present = {str(path.relative_to(ROOT)) for path in ROOT.rglob("*.lean")
               if ".lake" not in path.relative_to(ROOT).parts
               and ".git" not in path.relative_to(ROOT).parts}
    if present != lean_files:
        raise ValueError("Lean source inventory differs from the release manifest")
    for name in sorted(lean_files):
        text = (ROOT / name).read_text()
        if re.search(r"\b(?:sorry|admit|native_decide|unsafe|axiom)\b", lean_code(text)):
            raise ValueError("Prohibited proof construct in " + name)
        for line in text.splitlines():
            if line.startswith("import "):
                for module in line[7:].split():
                    if module.startswith(("ChenRanks", "checks")) or module == "Verification":
                        dependency = module.replace(".", "/") + ".lean"
                        if dependency not in lean_files:
                            raise ValueError("Missing project import: " + dependency)
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.29.0":
        raise ValueError("Unexpected Lean toolchain")
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    if not any(p["name"] == "mathlib" and p["rev"] == MATHLIB_REVISION for p in packages):
        raise ValueError("Unexpected Mathlib revision")
    return manifest_path, lean_files


def command(args):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise RuntimeError("Command failed: " + " ".join(args))
    return result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-sources", action="store_true",
                        help="check source hashes and imports without invoking Lean")
    parser.add_argument("--skip-build", action="store_true",
                        help="audit an already built project")
    args = parser.parse_args()
    manifest_path, lean_files = check_sources()
    if args.check_sources:
        print(f"Source integrity verified: {len(lean_files)} Lean modules.")
        return
    version = command(["lake", "env", "lean", "--version"]).strip()
    if not version.startswith("Lean (version 4.29.0,"):
        raise ValueError("The pinned Lean toolchain is required")
    mathlib = ROOT / ".lake/packages/mathlib"
    if command(["git", "-C", str(mathlib), "rev-parse", "HEAD"]).strip() != MATHLIB_REVISION:
        raise ValueError("The installed Mathlib checkout differs from the pinned revision")
    if command(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"]).strip():
        raise ValueError("The installed Mathlib checkout has tracked modifications")
    if args.skip_build:
        command(["lake", "--no-build", "--rehash", "build"])
    else:
        subprocess.run(["lake", "--rehash", "build"], cwd=ROOT, check=True)
    outputs = []
    queries = []
    for name in AUDITS:
        output = command(["lake", "env", "lean", name])
        outputs.append("=== " + name + " ===\n\n" + output)
        for declaration, raw in re.findall(
                r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
            axioms = sorted({re.sub(r"\.\{[^}]*\}", "", x.strip())
                             for x in raw.split(",") if x.strip()})
            if not set(axioms) <= FOUNDATIONS:
                raise ValueError("Unexpected axiom dependency: " + declaration)
            queries.append({"module": name, "declaration": declaration, "axioms": axioms})
        for declaration in re.findall(r"'([^']+)' does not depend on any axioms", output):
            queries.append({"module": name, "declaration": declaration, "axioms": []})
    expected_queries = Counter((module, declaration)
                               for module, declarations in EXPECTED_QUERIES.items()
                               for declaration in declarations)
    if Counter((q["module"], q["declaration"]) for q in queries) != expected_queries:
        raise ValueError("Incomplete theorem axiom audit")
    artifacts = {}
    for name in sorted(lean_files):
        artifact = ROOT / ".lake/build/lib/lean" / Path(name).with_suffix(".olean")
        if not artifact.is_file():
            raise ValueError("Missing compiled module: " + name)
        artifacts[name] = sha256(artifact)
    verification = ROOT / "verification"
    declaration_path = verification / "Declarations.txt"
    declaration_path.write_text("\n\n".join(outputs))
    certificate = {
        "schemaVersion": 1,
        "releaseVersion": "1.0.0",
        "result": "kernel-verified relative to one explicit AFRS input",
        "leanVersion": version,
        "mathlibRevision": MATHLIB_REVISION,
        "sourceManifest": "verification/SourceManifest.json",
        "sourceManifestSha256": sha256(manifest_path),
        "leanModuleCount": len(lean_files),
        "compiledModuleSha256": artifacts,
        "externalMathematicalInputs": [{
            "declaration": "ChenRanks.Koszul.AFRSEffectiveCanonicalDecomposition",
            "representation": "explicit theorem parameter hAFRS",
            "reference": "AFRS, The effective Chen Ranks Conjecture, Theorem 1.1 and its proof",
            "url": "https://arxiv.org/html/2512.10160v1",
        }],
        "mainTheorems": MAIN_THEOREMS,
        "ranges": {"affine": "q >= max(2, N-1)", "central": "q >= max(2, N-2)"},
        "axiomQueries": queries,
        "allowedFoundationalAxioms": sorted(FOUNDATIONS),
        "projectMathematicalAxioms": False,
        "proofHoles": False,
        "declarationOutput": "verification/Declarations.txt",
        "declarationOutputSha256": sha256(declaration_path),
    }
    build_report = ROOT / ".lake/release-build-report.json"
    if build_report.exists():
        build = json.loads(build_report.read_text())
        if build["exitCode"] != 0:
            raise ValueError("The recorded release build failed")
        binding = build.get("buildInputSha256", {})
        build_inputs = lean_files | {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        if set(binding) == build_inputs and all(
                sha256(ROOT / name) == expected for name, expected in binding.items()):
            certificate["releaseSourceBuild"] = {
                "freshProjectSourceBuild": build["freshProjectSourceBuild"],
                "projectArtifactsReused": build["projectArtifactsReused"],
                "dependencyCacheReused": build["mathlibCacheReused"],
                "exitCode": build["exitCode"],
                "buildInputSha256": binding,
            }
    (verification / "Certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    print(f"Verified {len(lean_files)} modules and {len(queries)} axiom queries; "
          "the sole external input is the explicit AFRS decomposition parameter.")


if __name__ == "__main__":
    main()
