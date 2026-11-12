KNOWNFILES    := Makefile
.DEFAULT_GOAL := invoke-coqmakefile-all

invoke-coqmakefile-all:
	$(MAKE) -C tulip-tla      $(MAKECMDGOALS)
	$(MAKE) -C tulip-tla-lib  $(MAKECMDGOALS)
	$(MAKE) -C examples/01-hour-clock  $(MAKECMDGOALS)
	$(MAKE) -C examples/02-proof-rules $(MAKECMDGOALS)

.PHONY: invoke-coqmakefile-all $(KNOWNFILES)

%: invoke-coqmakefile-all
	@true
