package jsy.lab3
import scala.util.Try


object Lab3 extends jsy.util.JsyApplication  {
import ast._
 /*
 * CSCI 3155: Lab 3
 * David Benson
 *
 * Partner: <Your Partner's Name>
 * Collaborators: <Any Collaborators>
 */




/*
 * Fill in the appropriate portions above by replacing things delimited
 * by '<'... '>'.
 *
 * Replace the '???' expression with your code in each function. The
 * '???' expression is a Scala expression that throws a NotImplementedError
 * exception.
 *
 * Your lab will not be graded if it does not compile.
 *
 * This template compiles without error. Before you submit comment out any
 * code that does not compile or causes a failing assert.  Simply put in a
 * '???' as needed to get something that compiles without error.
 */




/******************************************************/
/**************** Regular Section *********************/
/******************************************************/




/* Static Scoping */

def substitute(v: Expr, x: String, e: Expr): Expr = {
require(isValue(v), s"substitute: v ${v} to substitute is not a value")
def subst(e: Expr): Expr = substitute(v, x, e)
  e match {
  case N(_) | B(_) | Undefined | S(_) => e
  case Print(e1) => Print(subst(e1))
  case Unary(uop, e1) => Unary(uop, subst(e1))
  case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
  case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
  case Call(e1, e2) => Call(subst(e1), subst(e2))

  case Var(y) if x == y => v
  case Var(_) => e

  case Fun(None, y, e1) =>
    if (x == y) e
    else Fun(None, y, substitute(v, x, e1))

  case Fun(Some(y1), y2, e1) =>
    if (x == y2 || x == y1) e
    else Fun(Some(y1), y2, substitute(v, x, e1))

  case ConstDecl(y, e1, e2) =>
    if (x == y) ConstDecl(y, subst(e1), e2)
    else ConstDecl(y, subst(e1), subst(e2))

  }
}

def iterateBasic[A](acc0: A)(stepi: (A, Int) => Option[A]): A = {
def loop(acc: A, i: Int): A = {
  stepi(acc, i) match {
    case None => acc
    case Some(nextAcc) => loop(nextAcc, i + 1)
  }
}
loop(acc0, 0)
}


def iterate[Err, A](acc0: A)(stepi: (A, Int) => Option[Either[Err, A]]): Either[Err, A] = {
def loop(acc: A, i: Int): Either[Err, A] = {
  stepi(acc, i) match {
    case None => Right(acc)
    case Some(Left(err)) => Left(err)
    case Some(Right(nextAcc)) => loop(nextAcc, i + 1)
  }
}
loop(acc0, 0)
}


def toBoolean(e: Expr): Boolean = e match {
  case B(b) => b
  case N(n) => n != 0
  case S(s) => s.nonEmpty
  case Undefined => false
  case Fun(_, _, _) => true
  case _ => throw new MatchError(s"toBoolean: unsupported expression $e")
}


def stepBasic(e: Expr): Expr = e match {

  case Print(v1) if isValue(v1) =>
    println(pretty(v1))
    Undefined

  case Unary(Neg, N(n)) => N(-n)

  case Unary(Not, B(b)) => B(!b)

  case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
  case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)

  case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
  case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
  case Binary(Div, N(n1), N(n2)) => N(n1 / n2)

  case Binary(And, B(b1), B(b2)) => B(b1 && b2)

  case Binary(Or, B(b1), B(b2)) => B(b1 || b2)

  case If(B(true), e2, _) => e2
  case If(B(false), _, e3) => e3

  case Call(Fun(None, x, e1), v2) if isValue(v2) =>
    stepBasic(substitute(v2, x, e1))

  case Call(Fun(Some(f), x, e1), v2) if isValue(v2) =>
    val substituted = substitute(v2, x, e1)
    val recursiveSubstituted = substitute(Fun(Some(f), x, e1), f, substituted)
    stepBasic(recursiveSubstituted)

 /* Inductive Cases: Search Rules */

  case Unary(uop, e1) if !isValue(e1) => Unary(uop, stepBasic(e1))

  case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, stepBasic(e1), e2)

  case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, stepBasic(e2))

  case If(e1, e2, e3) => If(stepBasic(e1), e2, e3)

  case Call(e1, e2) if !isValue(e1) => Call(stepBasic(e1), e2)

  case Call(v1, e2) if isValue(v1) => Call(v1, stepBasic(e2))

  case _ => throw new MatchError(s"stepBasic: unsupported expression $e")
}


def stepCheck(e: Expr): Either[DynamicTypeError, Expr] = e match {

  case Print(v1) if isValue(v1) => println(pretty(v1)); Right(Undefined)
  case Print(e1) => stepCheck(e1).map(Print)

  // Handle functions (Fun) as values, they don't need further evaluation.
  case Fun(_, _, _) => Right(e)

  case Binary(Seq, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Seq, e1, e2))
  case Binary(Seq, e1, e2) if isValue(e1) => stepCheck(e2)

  case ConstDecl(y, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => ConstDecl(y, e1, e2))
  case ConstDecl(y, e1, e2) => Right(substitute(e1, y, e2))

  case If(e1, e2, e3) if !isValue(e1) => stepCheck(e1).map(e1 => If(e1, e2, e3))
  case If(e1, e2, e3) => {
    if (toBoolean(e1)) {
      if (isValue(e2)) Right(e2) else stepCheck(e2)
    } else {
      if (isValue(e3)) Right(e3) else stepCheck(e3)
    }
  }


  case Call(e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Call(e1, e2))
  case Call(e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Call(e1, e2))
  case Call(Fun(xopt, y, e1), e2) => {
    val noVarsBody = substitute(e2, y, e1)
    xopt match {
      case Some(x) => Right(substitute(Fun(xopt, y, e1), x, noVarsBody))
      case None    => Right(noVarsBody)
    }
  }
  case Call(e1, e2) => Left(DynamicTypeError(Call(e1, e2)))

  case Unary(Neg, N(x)) => Right(N(-x))
  case Unary(Neg, e1) if !isValue(e1) => stepCheck(e1).map(e1 => Unary(Neg, e1))
  case Unary(Neg, e1) => Left(DynamicTypeError(Unary(Neg, e1)))

  case Binary(And, e1, e2) => {
    (e1, e2) match {
      case (e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(And, e1, e2))
      case (e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(And, e1, e2))
      case (e1, e2) => if (!toBoolean(e1)) Right(e1) else Right(e2)
    }
  }

  case Binary(Plus, N(x), N(y)) => Right(N(x + y))
  case Binary(Plus, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Plus, e1, e2))
  case Binary(Plus, e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(Plus, e1, e2))
  case Binary(Plus, e1, e2) => Left(DynamicTypeError(Binary(Plus, e1, e2)))

  case Binary(Minus, N(x), N(y)) => Right(N(x - y))
  case Binary(Minus, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Minus, e1, e2))
  case Binary(Minus, e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(Minus, e1, e2))
  case Binary(Minus, e1, e2) => Left(DynamicTypeError(Binary(Minus, e1, e2)))

  case Binary(Times, N(x), N(y)) => Right(N(x * y))
  case Binary(Times, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Times, e1, e2))
  case Binary(Times, e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(Times, e1, e2))
  case Binary(Times, e1, e2) => Left(DynamicTypeError(Binary(Times, e1, e2)))

  case Binary(Eq, x, y) if isValue(x) && isValue(y) => Right(B(x == y))
  case Binary(Eq, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Eq, e1, e2))
  case Binary(Eq, e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(Eq, e1, e2))
  case Binary(Eq, e1, e2) => Left(DynamicTypeError(Binary(Eq, e1, e2)))

  case Binary(Div, N(x), N(y)) => Right(N(x / y))
  case Binary(Div, e1, e2) if !isValue(e1) => stepCheck(e1).map(e1 => Binary(Div, e1, e2))
  case Binary(Div, e1, e2) if !isValue(e2) => stepCheck(e2).map(e2 => Binary(Div, e1, e2))
  case Binary(Div, e1, e2) => Left(DynamicTypeError(Binary(Div, e1, e2)))

  /* Cases that should never match. Your cases above should ensure this. */
  case Var(_) => throw new AssertionError(s"Gremlins: internal error, not closed expression $e.")
  case v if isValue(v) => throw new AssertionError(s"Gremlins: internal error, step should not be called on values $v.")
}


/* IMPORTANT: Choose which version of step to use for testing by choosing one of the lines. You will pick one version to submit. */
//def step(e: Expr): Either[DynamicTypeError, Expr] = Right(stepBasic(e))
def step(e: Expr): Either[DynamicTypeError, Expr] = stepCheck(e)

/******************************************************/
/************ End Regular Section *********************/
/******************************************************/

/******************************************************/
/************ Accelerated Section *********************/
/******************************************************/


def toNumber(v: Expr): Double = {
  require(isValue(v))
  ???
}
 def toStr(v: Expr): String = {
  require(isValue(v))
  ???
}

def stepCoerce(e: Expr): Either[DynamicTypeError, Expr] = ???

/* Choose to use this version of step for testing uncommenting this line and commenting the definition of step above. */
//def step(e: Expr): Either[DynamicTypeError, Expr] = stepCoerce(e)




/******************************************************/
/************ End Accelerated Section *****************/
/******************************************************/




/* External Interfaces */
 //this.debug = true // comment this out or set to false if you don't want print debugging information
this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
this.keepGoing = true // comment this out if you want to stop at first exception when processing a file




/** Interface to take a small-step from a string. This is convenient for unit testing. */
def oneStep(s: String): Either[DynamicTypeError, Expr] = step(Parser.parse(s))




/** Interface to run your small-step interpreter and print out the steps of evaluation if debugging. */
def iterateStep(e: Expr): Either[DynamicTypeError, Expr] = {
  require(closed(e), s"iterateStep: ${e} not closed")
  if (debug) {
    println("------------------------------------------------------------")
    println("Evaluating with step ...")
  }
  val v = iterate(e) { (e: Expr, n: Int) =>
    if (debug) { println(s"Step $n: $e") }
    if (isValue(e)) None else Some(step(e))
  }
  if (debug) { println("Value: " + v) }
  v
}




/** Interface to run your small-step interpreter from a string. This is convenient for unit testing. */
def iterateStep(s: String): Either[DynamicTypeError, Expr] = iterateStep(Parser.parse(s))




/** Interface for main for JsyApplication */
def processFile(file: java.io.File): Unit = {
  if (debug) {
    println("============================================================")
    println("File: " + file.getName)
    println("Parsing ...")
  }




  val e1 =
    handle(None: Option[Expr]) {
      Some {
        Parser.parseFile(file)
      }
    } getOrElse {
      return
    }




  handle(()) {
    println("# Stepping ...")
    def loop(e: Expr, n: Int): Either[DynamicTypeError, Expr] = {
      println("## %4d: %s".format(n, e))
      if (isValue(e)) Right(e) else step(e) flatMap { e1 => loop(e1, n + 1) }
    }
    loop(e1, 0) match {
      case Right(v1) => println(pretty(v1))
      case Left(err) => println(err)
    }
  }
}




}
