from os import listdir
from functools import partial
import subprocess

cmd             = ["java", "-cp", "antlr-4.5.1-complete.jar:.", "tool.SRTool"]
correctSuffix   = "./tests/correct/"
incorrectSuffix = "./tests/incorrect/"

def appendSuffix(suffix, string) :
  return suffix + string

def runTests(expectedOuput, tests) :
  failedTests = []
  for test in tests :
    cmd.append(test)
    try :
      output = subprocess.check_output(cmd)
    except subprocess.CalledProcessError as exception:
      output = exception.output
    result = output.split('\n')[0]
    if result != expectedOuput :
      failedTests.append(test)
    cmd.pop()
  if len(failedTests) == 0 :
    print "All tests for", expectedOuput, "passed!!!"
  else :
    print len(failedTests), "tests failed for", expectedOuput, "failed!"
    print "Following tests failed:"
    for test in failedTests :
      print test

correctTests   = map(partial(appendSuffix, correctSuffix), listdir(correctSuffix))
incorrectTests = map(partial(appendSuffix, incorrectSuffix), listdir(incorrectSuffix))

runTests("CORRECT", correctTests)
runTests("INCORRECT", incorrectTests)
