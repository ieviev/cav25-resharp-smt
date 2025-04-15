FROM debian:bookworm-slim AS build

# install dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    time \
    netcat-traditional \
    curl \
    python3 \
    python3-pip \
    python3-setuptools \
    python3-wheel \
    python3-dev \
    python3.11-venv \
    git \
    build-essential  && \
    apt-get clean

# Ostrich deps

RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | tee /etc/apt/sources.list.d/sbt.list
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian /" | tee /etc/apt/sources.list.d/sbt_old.list
RUN curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | apt-key add
RUN apt-get update

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
   default-jdk-headless \
   sbt && \
   apt-get clean

# does not work
#RUN git clone --depth 1 --branch v1.4smtcomp https://github.com/uuverifiers/ostrich
WORKDIR /
RUN mkdir ostrich
WORKDIR /ostrich
RUN git init
RUN git remote add origin https://github.com/uuverifiers/ostrich
RUN git fetch --depth 1 origin 5b574473b9a875ae121c9bae2182e6047e7ace3a
RUN git checkout FETCH_HEAD
RUN sbt assembly
WORKDIR /

# Z3 deps
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
    cmake \
    make \
    clang \
    g++ \
    curl \
    default-jdk-headless \
    python3 \
    python3-setuptools && \
    apt-get clean

RUN git clone --depth 1 --branch z3-4.13.4  https://github.com/Z3Prover/z3

WORKDIR /z3
RUN python3 scripts/mk_make.py
WORKDIR /z3/build/
RUN make -j$(nproc)
RUN strip /z3/build/z3
#RUN make install   

#CVC5 deps
WORKDIR /
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get install cmake \
    python3-tomli \
    python3-pyparsing \
    libgmp-dev && \
    apt-get clean

WORKDIR /
RUN mkdir cvc5
WORKDIR /cvc5
RUN git init
RUN git remote add origin https://github.com/cvc5/cvc5
RUN git fetch --depth 1 origin 929f2ac4e9f2507901a08d83f12024d67f9a8764
RUN git checkout FETCH_HEAD
RUN ./configure.sh --static --static-binary --auto-download --name=prod
WORKDIR /cvc5/prod
RUN make -j$(nproc)
RUN strip /cvc5/prod/bin/cvc5
#RUN make install
WORKDIR /


#Z3-noodler deps

RUN git clone --depth 1 --branch 1.7.1 https://github.com/VeriFIT/mata.git
WORKDIR /mata
RUN make -j$(nproc) release
RUN make install
WORKDIR /

RUN git clone --depth 1 --branch v1.3.0  https://github.com/VeriFIT/z3-noodler
WORKDIR /z3-noodler/build/
RUN cmake -DCMAKE_BUILD_TYPE=Release ..
RUN make -j$(nproc)
RUN mv /z3-noodler/build/z3 /z3-noodler/build/z3-noodler
RUN strip /z3-noodler/build/z3-noodler
WORKDIR /

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
    unzip \
    wget && \
    apt-get clean

RUN mkdir /z3str4
WORKDIR /z3str4
RUN wget https://zenodo.org/records/10041441/files/tacas24-artifact.zip?download=1 -O tacas24-artifact.zip && \
    unzip -p  tacas24-artifact.zip tacas24-artifact/tools/z3str4 > z3str4 && \
    rm tacas24-artifact.zip && \
    chmod +x z3str4
WORKDIR /

# #Ostrich RECL (SETTA 2023) and dependencies
RUN git clone --depth 1 --branch setta_2023 https://github.com/SimpleXiaohu/ostrich ostrichrecl
WORKDIR /ostrichrecl
RUN sed -i 's|2\.13\.8|2.13.10|g' build.sbt
RUN git clone --depth 1 --branch oopsla24-submission https://github.com/amandasystems/catra
WORKDIR /ostrichrecl/catra
RUN sed -i 's|lazy val princess = "uuverifiers" %% "princess" % "nightly-SNAPSHOT"|lazy val princess = "io.github.uuverifiers" %% "princess" % "2023-06-19"|g' project/Dependencies.scala
RUN sbt assembly
WORKDIR /ostrichrecl
RUN mkdir lib
RUN mv catra/target/scala-2.13/uuverifiers/catra-assembly-0.1.4.jar lib/
RUN wget https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.1.0-linux64.tar.xz -O nuXmv-2.1.0-linux64.tar.xz
RUN tar xJf nuXmv-2.1.0-linux64.tar.xz
RUN rm nuXmv-2.1.0-linux64.tar.xz
RUN mkdir bin
RUN mv nuXmv-2.1.0-linux64/bin/nuXmv bin/nuxmv
ENV PATH="$PATH:/ostrichrecl/bin"
RUN sbt assembly
RUN mv ostrich ostrichrecl
RUN sed -i -e '43,45d' ostrichrecl
WORKDIR /

# # z3-alpha
WORKDIR /
RUN mkdir z3alpha
WORKDIR /z3alpha
RUN git init
RUN git remote add origin https://github.com/JohnLyu2/z3alpha
RUN git fetch --depth 1 origin dd7435151c0ee0c583f571612d72110e1c5ecc22
RUN git checkout FETCH_HEAD

# latex to generate the plot pdf
#RUN apt-get install -y texlive-latex-extra cm-super ghostscript && apt-get clean
# For generating the PNG version of the plot.
RUN apt-get install -y texlive-latex-extra cm-super dvipng && apt-get clean

# dotnet for scripts
#RUN wget https://dot.net/v1/dotnet-install.sh && chmod +x ./dotnet-install.sh && ./dotnet-install.sh --channel 9.0 && rm ./dotnet-install.sh
RUN wget https://packages.microsoft.com/config/debian/12/packages-microsoft-prod.deb -O packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    rm packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y dotnet-sdk-9.0 && \
    apt-get clean
ENV DOTNET_CLI_TELEMETRY_OPTOUT="true"
ENV DOTNET_NOLOGO="true"

# install nightly rust
ENV RUSTUP_HOME=/rust
ENV CARGO_HOME=/cargo
ENV PATH=/cargo/bin:/rust/bin:$PATH 
RUN echo "(curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly --no-modify-path) && rustup default nightly" > /install-rust.sh && chmod 755 /install-rust.sh
RUN /install-rust.sh && rm /install-rust.sh

# setup python venv
WORKDIR /python
COPY requirements.txt /python/requirements.txt
RUN python3 -m venv /python/venv && cd /python && . venv/bin/activate && python3 -m pip install -r /python/requirements.txt
ENV PATH="/python/venv/bin/:~/.dotnet/:$PATH"

WORKDIR /

# Compile resharp-solver
COPY source /source
WORKDIR /source/resharp-solver
RUN cargo +nightly build --release

WORKDIR /
RUN mkdir tools 
COPY tools/*.sh /tools/ 
RUN ln -s /z3/build/z3 /tools/z3 
RUN ln -s /cvc5/prod/bin/cvc5 /tools/cvc5 
RUN ln -s /ostrich/ostrich /tools/ostrich 
RUN ln -s /ostrichrecl/ostrichrecl /tools/ostrichrecl 
RUN ln -s /z3alpha/smtcomp24/z3alpha.py /tools/z3alpha.py
RUN ln -s /z3-noodler/build/z3-noodler /tools/z3-noodler
RUN ln -s /z3str4/z3str4 /tools/z3str4
RUN ln -s /source/resharp-solver/target/release/resharp-solver /tools/resharp-solver
RUN mkdir -p /figs/data
RUN mkdir -p /results

# Copy benchmark data
WORKDIR /
COPY inputs /inputs
COPY formulae /formulae
COPY scripts /scripts
COPY pyco_proc /pyco_proc
COPY run_bench.sh /run_bench.sh
COPY run_bench_singlerun.sh /run_bench_singlerun.sh

CMD ["/bin/bash"]
