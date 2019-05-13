# cubical_forcing

This compiles using the `coq-8.8` branch of coq, and the up `update-translation-plugin` of metacoq. Note that the latter does not compile completely, but a 
  # make translations
compiles enough for our purpose.

Detailed installation instruction:
If you alredy have a working installation of the right version of Coq and of Metacoq (for example through opam), then simply modify the `_Coqproject` file so that it points to the right location. What follows are the instructions for a full installation from scratch.

  - Create a directory <instal dir> and go in it.
  ```
  mkdir forcing
  cd forcing
  ```
  - Download and build the right version of Coq
  ```
  git clone https://github.com/coq/coq.git
  cd coq/
  git checkout -b coq.8.8 origin/v8.8
  ./configure -local
  make -j4
  cd ..
  ```
  - Set your command lin to use the right directory:
  ```
  export COQBIN=/path/to/the/directory/forcing/coq/bin/
  ```
  - Dowload right version of Metacoq
  ```
  git clone https://github.com/MetaCoq/metacoq.git
  cd metacoq
  git checkout -b update-translation origin/update-translation-plugin
  ```
  - In order to compile using the version of Coq built earlier we need to modify the files `tempalte-coq/Makefile` and `translations/Makefile`: in both cases, replace the line 
  ```
   coq_makefile -f _CoqProject -o Makefile.coq
   ```
by the following
   ```
  $(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
   ```
We can now build metacoq:
  ```
  make translations
  ```
This command should fail in some file in `translations`. The important part is that the file `translation_utils` gets built.
  - You can now download and build this repository:
  ```
  cd ..
  git clone https://github.com/MaximeLucasSky/cubical_forcing.git
  cd cubical_forcing
  ../coq/bin/coq_makefile -f _CoqProject -o Makefile
  make
  ```

