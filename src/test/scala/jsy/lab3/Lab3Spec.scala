package jsy.lab3

import org.scalatest.flatspec.AnyFlatSpec
import Parser.parse
import ast._
import Lab3._

class Lab3StudentSpec extends AnyFlatSpec {

  // Test 1: Higher-Order Function
  "StudentSpec" should "evaluate a higher order function" in {
    // JavaScripty code for higher-order function
    val jsyStr: String = """
      const applyTwice = function(f) { return function(x) { return f(f(x)); }; };
      const addOne = function(x) { return x + 1; };
      applyTwice(addOne)(3);
    """
    val answer: Either[DynamicTypeError, Expr] = Right(N(5)) // applyTwice(addOne)(3) should return 5
    assert(answer === iterateStep(parse(jsyStr)))
  }

  // Test 2: Recursive Function
  it should "evaluate a recursive factorial function" in {
    val jsyStr: String =
      """
        const fact = function f(x) {
          if (x === 0) 1 else x * f(x - 1)
        };
       fact(5);
      """
    val answer: Either[DynamicTypeError, Expr] = Right(N(120))
    assert(answer === iterateStep(parse(jsyStr)))
}


  // Test 3: Square Function
  it should "evaluate your test case" in {
    // JavaScripty code for the square function
    val jsyStr: String = """
      const square = function(x) { return x * x; };
      square(5);
    """
    val answer: Either[DynamicTypeError, Expr] = Right(N(25)) // square(5) should return 25
    assert(answer === iterateStep(parse(jsyStr)))
  }
}



class Lab3Spec extends AnyFlatSpec {

  "substitute" should "perform syntatic substitution respecting shadowing" in {
    val xplus1 = parse("x + 1")
    val twoplus1 = parse("2 + 1")
    assert(substitute(N(2), "x", xplus1) === twoplus1)
    val constx3 = parse("const x = 3; x")
    val shadowx = Binary(Plus, constx3, Var("x"))
    assert(substitute(N(2), "x", shadowx) === Binary(Plus, constx3, N(2)))
  }

  "iterateBasic" should "work for sumTo(100)" in {
    def sumTo(n: Int) = {
      iterateBasic(0) { case (acc, i) =>
        require(n >= 0)
        if (i > n) None
        else Some(acc + i)
      }
    }

    assertResult(5050) { sumTo(100) }
  }

  {
    def sumTo(n: Int): Either[String, Int] = {
      iterate(0) { case (acc, i) =>
        if (n < 0) Some(Left("requirement failed"))
        else if (i > n) None
        else Some(Right(acc + i))
      }
    }

    "iterate" should "work for sumTo(100)" in {
      assertResult(Right(5050)) { sumTo(100) }
    }

    "iterate" should "work for sumTo(-1)" in {
      assertResult(Left("requirement failed")) { sumTo(-1) }
    }

    val one = parse("1")

    it should "stop if the callback body returns None" in {
      assertResult(Right(one)) {
        iterate(one) { (_, _) => None }
      }
    }

    it should "increment the loop counter on each iteration and use e if the callback body returns Some(e)" in {
      assertResult(Right(parse("--1"))) {
        iterate(one) { (e: Expr, n: Int) =>
          if (n == 2) None else Some(Right(Unary(Neg, e)))
        }
      }
    }
  }

  "step/call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Fun(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === Right(N(3)))
  }

  it should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Fun(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === Right(N(6)))
  }


  /* Some tests based on rules */

  {
    val xval = N(2)
    val varx = Var("x")

    val e1 = parse("2 - 1 - 1")
    val e1p = parse("1 - 1")
    val e2 = parse("3 - 1 - 1")
    val e2p = parse("2 - 1")
    val v1 = N(0)
    val v2 = N(1)

    val vidfunction = parse("function (x) { return x }")

    "DoNeg" should "perform DoNeg" in {
      val np = -0
      assertResult(Right(N(np))) {
        step(Unary(Neg, v1))
      }
    }

    "SearchUnary" should "perform SearchUnary" in {
      assertResult(Right(Unary(Neg, e1p))) {
        step(Unary(Neg, e1))
      }
    }

    val e_callerror = Call(N(1), N(2))

    "TypeErrorCall" should "perform TypeErrorCall" in {
      assertResult(Left(DynamicTypeError(e_callerror))) {
        step(e_callerror)
      }
    }
  }
}

class Lab3JsyTests extends jsy.tester.JavascriptyTester(None, "lab3", Lab3)