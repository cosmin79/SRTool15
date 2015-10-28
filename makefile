compile:
	javac -cp antlr-4.5.1-complete.jar -Xlint:unchecked */*.java

run:
	./srtool . tests/mytests/complexIf.c

test:
	java -cp .:antlr-4.5.1-complete.jar tests.Test

clean:
	find . -name "*.class" -type f -delete

.PHONY: compile
