COQMF := CoqMakefile.mk

all: $(COQMF)
	$(MAKE) -f $(COQMF)

$(COQMF): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMF)

clean:
	-$(MAKE) -f $(COQMF) clean
	rm -f $(COQMF) $(COQMF).conf

.PHONY: all clean
