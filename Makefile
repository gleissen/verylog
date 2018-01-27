APP=verylog
FILE=src/verilog.pl

all: $(APP)

$(APP): $(APP).sav
	spld --output="$(APP)" \
		--main=restore \
		--moveable \
		--static \
		--resources-from-sav \
		--resources=$(APP).sav=/$(APP)/$(APP).sav

$(APP).sav: $(FILE)
	sicstus --goal "compile('$(FILE)'), save_program('$(APP).sav'), halt."
clean :
	rm $(APP) $(APP).sav
