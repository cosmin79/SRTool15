from os import listdir
from functools import partial
import subprocess
import os

cmd             = ["./srtool"]
correctSuffix   = "./tests/%s/correct/"
incorrectSuffix = "./tests/%s/incorrect/"

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

subprocess.call(["make"]);

correctTests = [correctSuffix % (folder) + file for folder in listdir("tests") if (os.path.isdir("tests/" + folder)) \
                     for file in listdir(correctSuffix % (folder))]

incorrectTests = [incorrectSuffix % (folder) + file for folder in listdir("tests") if (os.path.isdir("tests/" + folder)) \
                for file in listdir(incorrectSuffix % (folder))]

runTests("CORRECT", correctTests)
runTests("INCORRECT", incorrectTests)
