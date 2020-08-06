BUILD_DIR:=.build

MAIN_DEFN_FILE := hcs

k_files := $(MAIN_DEFN_FILE).k

java_dir    := $(BUILD_DIR)/java

java_kompiled    := $(java_dir)/$(MAIN_DEFN_FILE)-kompiled/timestamp

.PHONY: all default clean build verify

default: all

all: verify

clean:
	@rm -rf $(BUILD_DIR)

build: $(java_kompiled)

$(java_kompiled): $(java_files)
	kompile --backend java $(MAIN_DEFN_FILE).k --directory $(java_dir)

verify: $(java_kompiled)
	@$(foreach file, $(wildcard *-spec.k), echo 'proving' $(file) '...' && kprove --ignore-missing-smtlib-warning --directory $(java_dir) $(file);)

