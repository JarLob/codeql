import json
from pathlib import Path


QUERY = "codeql/actions-queries:Security/CWE-367/UntrustedCheckoutTOCTOUCritical.ql"
WORKFLOW = ".github/workflows/toctou.yml"


def test_toctou_results_are_grouped_by_checkout(codeql, actions):
    codeql.database.create(source_root="src")

    sarif_path = Path("results.sarif")
    codeql.database.analyze(
        "test-db",
        QUERY,
        format="sarif-latest",
        output=sarif_path,
        rerun=True,
    )

    sarif = json.loads(sarif_path.read_text())
    results = sarif["runs"][0]["results"]

    assert len(results) == 2
    assert {
        result["locations"][0]["physicalLocation"]["artifactLocation"]["uri"]
        for result in results
    } == {WORKFLOW}
    assert sorted(
        result["locations"][0]["physicalLocation"]["region"]["startLine"]
        for result in results
    ) == [14, 24]
    assert [len(result["codeFlows"]) for result in results] == [2, 2]