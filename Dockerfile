# Using the Ubuntu image (our OS)
FROM ubuntu:22.04
# Update package manager (apt-get) 
# and install (with the yes flag `-y`)
# Python and Pip
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip

# Allow statements and log messages to immediately appear in the Knative logs
ENV PYTHONUNBUFFERED True

# Copy local code to the container image.
ENV APP_HOME /app
WORKDIR $APP_HOME
COPY web_serv ./web_serv
COPY data ./data

# Install production dependencies.
RUN pip install --no-cache-dir -r web_serv/requirements.txt

EXPOSE 5000
# Run the web service on container startup. Here we use the gunicorn
# webserver, with one worker process and 8 threads.
# For environments with multiple CPU cores, increase the number of workers
# to be equal to the cores available.
# Timeout is set to 0 to disable the timeouts of the workers to allow Cloud Run to handle instance scaling.
WORKDIR $APP_HOME/web_serv   
CMD exec gunicorn --bind :5000 --workers 1 --threads 8 --timeout 0 wsgi:app