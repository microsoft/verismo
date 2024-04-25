FROM test-fs/benchmark
RUN apk add --update git perl build-base && \
    rm -rf /var/cache/apk/* && \
    git clone https://github.com/kdlucas/byte-unixbench.git /app
COPY ./context1.c /app/UnixBench/src/
#RUN echo "http://dl-cdn.alpinelinux.org/alpine/v3.8/community" >> /etc/apk/repositories
#RUN apk add php7 && \
#    rm -rf /var/cache/apk/* && \
#    cd ~ && git clone https://github.com/cloudharmony/unixbench.git

#COPY ./test.sh ~/unixbench/test.sh
#RUN chmod +x test.sh
