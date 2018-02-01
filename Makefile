APP=vcgen
MAIN_FILE=src/verilog.pl
OTHER_FILES=$(wildcard src/lib/*.pl)

all: $(APP)

$(APP): $(APP).sav
	spld --output="$(APP)" \
		--main=restore \
		--moveable \
		--static \
		--resources-from-sav \
		--resources=$(APP).sav=/$(APP)/$(APP).sav

$(APP).sav: $(MAIN_FILE) $(OTHER_FILES)
	sicstus --goal "compile('$<'), save_program('$(APP).sav'), halt."
clean :
	rm -f $(APP) $(APP).sav
