"""Reuse the existing benchmark dependency pins without fetching another Mathlib tree."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE.parent / "lake-manifest.json").read_text())
manifest["name"] = "floatlibCommunity"
manifest["packagesDir"] = "../../.lake/packages"
for package in manifest["packages"]:
    if package["type"] == "path":
        package["dir"] = "../" + package["dir"]
target = HERE / "lake-manifest.json"
text = json.dumps(manifest, indent=2) + "\n"
if not target.exists() or target.read_text() != text:
    target.write_text(text)
