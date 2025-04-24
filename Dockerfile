FROM ghcr.io/rems-project/cn:release

RUN apt-get install -y software-properties-common zip && \
    add-apt-repository ppa:deadsnakes/ppa && \
    apt-get install -y python3.13-full && \
    ln -s /usr/bin/python3.13 /usr/bin/python

RUN python -m ensurepip && \
    python -m pip install mkdocs-material mkdocs-macros-plugin

# ZKA: IMO, this should be done in the CN image itself...
RUN echo >> ~/.bashrc && echo >> ~/.bashrc && \
    echo "test -r /root/.opam/opam-init/init.sh && . /root/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true" >> ~/.bashrc
