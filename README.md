SRTool

In this project we implemented SRTool, a tool that aims to prove correctness or detect bugs in Simple C programs. Those programs are able to support loops, multiple procedures as well as constructs such as pre-post condtions and invariants. 

Overview

We applied standard and precise Software Reliability techniques for non-loop code like Predication. It is common knolwedge that for analyzing loops there isn't a perfect approach so we used both under-aproximation techniques like BMC and over-aproximation techniques like Loop Summarisation combined with Invariant Generation and Houdini.. We also implemented simple version of Dyanamic Symbolic Execution with the purpose of detecting bugs, by running a C++ equivalent program with symbolic inputs (e.g. for functions parameters) produced by our tool. We run many strategies in parallel ; some attempting to prove correctness, other searching for bugs. As a result, we hope we're able to catch a variety of scenarios. Our tool also gracefully reports unknown in the case in which a decision cannot be made about a program using our strategies. 

Reliability

We hope we have fixed most of the bugs we had in previous versions. We mention that upon running our tool on a set of 300+ hidden tests as part of the evaluation, we achieved 100% accuracy, although not 100% precision (we still reported some unknowns). However, given that the project was completed in a time frame of 5 - 6 weeks, there may still be some bugs we are not aware of.
