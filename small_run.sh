#!/bin/bash
set -e
python scripts/finetune_codet5.py small ids
python scripts/evaluate_sample_codet5.py small ids
python scripts/finetune_codet5.py small lemma ids
python scripts/evaluate_sample_codet5.py small lemma ids
