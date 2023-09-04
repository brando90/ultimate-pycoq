from pathlib import Path
import json

thm_json = json.load(open(Path('extracted_theorems.json').expanduser()))

print(f"There are {len(thm_json)} theorems")
