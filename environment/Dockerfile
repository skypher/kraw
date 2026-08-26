FROM ubuntu:24.04@sha256:33ceb71981b602c1a7443a53469e4dba065f7503eab3078a2d7a57a2ab987517

ARG DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    PYTHONHASHSEED=0 \
    PYTHONUNBUFFERED=1 \
    TZ=Etc/UTC

COPY environment/ubuntu.sources /etc/apt/sources.list.d/ubuntu.sources

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates \
       g++=4:13.2.0-7ubuntu1 \
       g++-13=13.3.0-6ubuntu2~24.04.1 \
       libboost1.83-dev=1.83.0-2.1ubuntu3.2 \
       libgmp-dev=2:6.3.0+dfsg-2ubuntu6.1 \
       lmodern=2.005-1 \
       make=4.3-4.1build2 \
       poppler-utils=24.02.0-1ubuntu9.9 \
       python3=3.12.3-0ubuntu2.1 \
       python3-pip=24.0+dfsg-1ubuntu1.3 \
       qpdf=11.9.0-1.1ubuntu0.1 \
       texlive-fonts-recommended=2023.20240207-1 \
       texlive-latex-base=2023.20240207-1 \
       texlive-latex-extra=2023.20240207-1 \
       texlive-pictures=2023.20240207-1 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /workspace
COPY requirements.txt /workspace/requirements.txt
RUN python3 -u -m pip install --break-system-packages --require-hashes \
    -r requirements.txt

COPY . /workspace

CMD ["make", "audit-fast"]
