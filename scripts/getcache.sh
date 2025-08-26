#!bin/bash
gcloud storage rsync   gs://leanaide_data/cache/prompt .leanaide_cache/prompt  --recursive
gcloud storage rsync   gs://leanaide_data/cache/prompt .leanaide_cache/prompt  --recursive