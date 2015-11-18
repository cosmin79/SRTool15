CLASSES = \
	*/*.java \
	tool/strategy/*.java \
	ast/*/*.java \
	ast/*/*/*.java

compile:
	javac -cp antlr-4.5.1-complete.jar $(CLASSES)

clean:
	find . -name "*.class" -type f -delete

.PHONY: compile
