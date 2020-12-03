EXEC=tests
COMP=ocamlc

all: $(EXEC)

$(EXEC): parser_.cmo SOS_.cmo main_.cmo test_while.cmo
	$(COMP) $^ -o $(EXEC)
	
test_while.cmo: test_while.ml grammar_.cmo SOS_.cmo parser_.cmo main_.cmo
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
	rm -rf *.cmi *.cmo *~
