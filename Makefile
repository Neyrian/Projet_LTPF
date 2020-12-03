EXEC=tester debugger
COMP=ocamlc

all: $(EXEC)

debugger: parser_.cmo SOS_.cmo main_.cmo debugger_.cmo
	$(COMP) $^ -o $@
	
tester: parser_.cmo SOS_.cmo main_.cmo tester_.cmo
	$(COMP) $^ -o $@
	
tester_.cmo: tester_.ml grammar_.cmo SOS_.cmo parser_.cmo main_.cmo
	$(COMP) -c $<
	
debugger_.cmo: debugger_.ml grammar_.cmo SOS_.cmo parser_.cmo main_.cmo
	$(COMP) -c $<
	
main_.cmo: main_.ml grammar_.cmo SOS_.cmo
	$(COMP) -c $<
	
SOS_.cmo: SOS_.ml grammar_.cmo
	$(COMP) -c $<
	
parser_.cmo: parser_.ml grammar_.cmo
	$(COMP) -c $<
	
grammar_.cmo: grammar_.ml
	$(COMP) -c $<
	
clean:
	rm -rf *.cmi *.cmo *~ $(EXEC)
