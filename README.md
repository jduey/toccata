Toccata
=======

A Clojure-inspired Lisp dialect that compiles to native executable using the Clang compiler

This is very much WFM code. Not suitable for any useful purpose.

You can learn more about Toccata by following the [blog here](http://toccata.io)

Quick Start
===========

Make sure the Clang compiler is installed and runnable
  On OSX, it's part of the Xcode package. You can run 'clang -v' to check.

Clone this repo

cd to the repo directory

run the 'scripts/build' script.
  This will compile the 'toccata' executable and then use that to compile 'examples/hello.toc' and execute it. You should see 'Howdy, Universe!!!' as the final output.

Rebuilding Toccata
=========

Run './toccata toccata.toc > toccata.c'

Then you can re-run the 'build' script.

Good luck!!!
