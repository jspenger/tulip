# File adapted from the Coq reference manual:
# https://rocq-prover.org/doc/V8.9.1/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

KNOWNTARGETS  := CoqMakefile
KNOWNFILES    := Makefile _CoqProject
.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
	@true
