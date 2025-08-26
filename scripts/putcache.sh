#!/bin/bash
gcloud storage rsync .leanaide_cache/chat/  gs://leanaide_data/cache/chat --recursive
gcloud storage rsync .leanaide_cache/prompt/  gs://leanaide_data/cache/prompt --recursive
