CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
PL_DIR = pl
ASSIGNMENT_DIR = Assignment

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

PL_FLAG = -R $(PL_DIR) PL -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

DEP_FLAG = -R $(PL_DIR) PL -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FILE_NAMES = \
   SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

   
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
   
COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
    
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

PL_FILE_NAMES = \
    Syntax.v SimpleProofsAndDefs.v InductiveType.v DenotationalBasic.v RecurProp.v BuiltInNat.v DenotationalRels.v Logic.v FixedPoint.v Monad.v List.v Monad2.v StateRelMonad.v
	
PL_FILES=$(PL_FILE_NAMES:%.v=$(PL_DIR)/%.v)

ASSIGNMENT_FILE_NAMES = \
	 Assignment1025b.v Assignment1029.v Assignment1108a.v Assignment1206a.v Assignment1206b.v

ASSIGNMENT_FILES=$(ASSIGNMENT_FILE_NAMES:%.v=$(ASSIGNMENT_DIR)/%.v)

FILES = $(PL_FILES) \
  $(SETS_FILES) \
  $(COMPCERT_FILES) \
	$(ASSIGNMENT_FILES)

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(SETS_FLAG) $<

$(COMPCERT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(COMPCERT_FLAG) $<
			
$(PL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F);
	@$(COQC) $(PL_FLAG) $<

$(ASSIGNMENT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F);
	@$(COQC) $(PL_FLAG) $<

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob;
	@rm -f *.vo */*.vo;
	@rm -f *.vok */*.vok;
	@rm -f *.vos */*.vos;
	@rm -f .*.aux */.*.aux;
	@rm -f .depend;

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
