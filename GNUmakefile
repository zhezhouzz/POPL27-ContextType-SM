.DEFAULT_GOAL := all

ROCQMAKEFILE := Makefile.coq
ROCQPROJECT := _CoqProject
PROJECT_FLAGS := $(shell awk '/^-R / { printf "%s %s %s ", $$1, $$2, $$3 }' $(ROCQPROJECT))

all: $(ROCQMAKEFILE)
	@$(MAKE) -f $(ROCQMAKEFILE) all

clean: $(ROCQMAKEFILE)
	@$(MAKE) -f $(ROCQMAKEFILE) clean

environment:
	@rocq --version
	@printf "OCaml " && ocamlc -version
	@opam list --installed rocq-core rocq-stdlib rocq-stdpp --columns=name,version

check-admits:
	@echo "Checking that the Rocq sources contain no admitted proofs..."
	@if grep -R -n -E 'Admitted\.|admit\.' --include='*.v' .; then \
		echo "Unexpected admitted proof found."; exit 1; \
	else \
		echo "No Admitted./admit. commands found."; \
	fi

print-assumptions: all
	@echo "Printing assumptions of the top-level soundness theorems..."
	@rocq c $(PROJECT_FLAGS) ContextTyping/theories/SoundnessAssumptions.v

kernel-check: all
	@echo "Kernel-checking the soundness development..."
	@rocqchk -silent $(PROJECT_FLAGS) ContextTyping.Soundness
	@echo "Kernel check completed successfully."

artifact-check: all
	@$(MAKE) --no-print-directory environment
	@$(MAKE) --no-print-directory check-admits
	@$(MAKE) --no-print-directory print-assumptions
	@$(MAKE) --no-print-directory kernel-check
	@echo "Artifact check completed successfully."

$(ROCQMAKEFILE): $(ROCQPROJECT)
	@rocq makefile -f $(ROCQPROJECT) -o $(ROCQMAKEFILE)

.PHONY: all clean environment check-admits print-assumptions kernel-check artifact-check
