from os import listdir
from functools import partial
import subprocess
import os

from multiprocessing.pool import ThreadPool

correctSuffix   = "./tests/%s/correct/"
incorrectSuffix = "./tests/%s/incorrect/"

def appendSuffix(suffix, string) :
  return suffix + string

def runTest(expectedOutput, test):
  cmd = ["./srtool"]
  cmd.append(test)
  try :
    output = subprocess.check_output(cmd)
  except subprocess.CalledProcessError as exception:
    output = exception.output
  result = output.split('\n')[0]

  return (test, result)

def runTests(expectedOutput, tests):
  results = []
  pool = ThreadPool(len(tests))
  for test in tests:
    results.append(pool.apply_async(runTest, args=(expectedOutput, test)))
  pool.close()
  pool.join()

  results = map(lambda future: future.get(), results)
  failedTests = filter(lambda (test, actual): expectedOutput != actual, results)
  failedTests = map(lambda (test, actual): test, failedTests)

  if len(failedTests) == 0:
    print "All tests for %s passed!!!" % (expectedOutput)
  else:
    print len(failedTests), "tests failed for %s!" % (expectedOutput)
    print "Following tests failed:"
    for test in failedTests :
      print "Test %s failed\n" % (test)


subprocess.call(["make"])

correctTests = [correctSuffix % (folder) + file for folder in listdir("tests") if (os.path.isdir("tests/" + folder)) \
                     for file in listdir(correctSuffix % (folder))]

incorrectTests = [incorrectSuffix % (folder) + file for folder in listdir("tests") if (os.path.isdir("tests/" + folder)) \
                for file in listdir(incorrectSuffix % (folder))]

runTests("CORRECT", correctTests)
runTests("INCORRECT", incorrectTests)