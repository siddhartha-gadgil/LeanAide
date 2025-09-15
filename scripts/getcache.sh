#!/bin/bash
gcloud storage rsync   gs://leanaide_data/cache/prompt .leanaide_cache/prompt  --recursive || gsutil -m cp -r gs://leanaide_data/cache/prompt .leanaide_cache/
gcloud storage rsync   gs://leanaide_data/cache/chat .leanaide_cache/chat  --recursive || gsutil -m cp -r gs://leanaide_data/cache/chat .leanaide_cache/