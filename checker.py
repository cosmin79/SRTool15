from os import listdir
from functools import partial
import subprocess
import os

from multiprocessing.pool import Pool
from multiprocessing import cpu_count

correctSuffix   = "./tests/%s/correct/"
incorrectSuffix = "./tests/%s/incorrect/"

def prepareOutputfile():
  output = "log/"
  try:
    output += subprocess.check_output(["git", "rev-parse", "HEAD"])
    output = output.split("\n")[0]
  except subprocess.CalledProcessError as exception:
    output += "gitGetCommitFailed"
    print exception.output
  output += ".txt"
  return output

def runTest(test):
  cmd = ["./srtool"]
  cmd.append(test)
  try :
    output = subprocess.check_output(cmd)
  except subprocess.CalledProcessError as exception:
    output = exception.output
  result = output.split('\n')[0]

  return (test, result)

def runTests(expectedOutput, tests, outputFile):
  results = []
  pool = Pool(4)
  for test in tests:
    print test
    results.append(pool.apply_async(runTest, args=(test,)))
  pool.close()
  pool.join()

  results = map(lambda future: future.get(), results)
  failedTests = []
  for (test, result) in results:
    message = ""
    if (result != expectedOutput):
      message = "FAIL: expected: %s, actual: %s" % (expectedOutput, result)
      failedTests.append(test)
      outputFile.write(test + " " + message + "\n")

  outputFile.write("--------------------------------------------------------\n")
  outputFile.write("Summary: \n")
  if (len(failedTests) == 0):
    outputFile.write("Congrats! All tests passed!\n")
  else:
    outputFile.write(str(len(failedTests)) + " tests have failed!\n")

subprocess.call(["make"])

correctTests = [correctSuffix % (folder) + file \
                for folder in listdir("tests") \
                  if (os.path.isdir("tests/" + folder)) \
                     for file in listdir(correctSuffix % (folder))]

incorrectTests = [incorrectSuffix % (folder) + file \
                  for folder in listdir("tests") \
                    if (os.path.isdir("tests/" + folder)) \
                      for file in listdir(incorrectSuffix % (folder))]

f = open(prepareOutputfile(), "w+")
try:
  runTests("CORRECT", correctTests, f)
  runTests("INCORRECT", incorrectTests, f)
finally:
  f.close()
