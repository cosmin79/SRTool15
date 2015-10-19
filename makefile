compile:
	javac -cp antlr-4.5.1-complete.jar -Xlint:unchecked */*.java

clean:
	find . -name "*.class" -type f -delete

.PHONY: compile
