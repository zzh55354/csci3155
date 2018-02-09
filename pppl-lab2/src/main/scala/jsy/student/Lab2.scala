package jsy.student

import jsy.lab2.Lab2Like
import jsy.student.Lab2.{eval, toNumber}

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */



  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   *
   * You can catch an exception in Scala using:
   * try ... catch { case ... => ... }
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true)  => 1
      case S(s) => try {s.toDouble} catch {case _: NumberFormatException => Double.NaN}
      case Undefined => Double.NaN
      case _ => ???
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(0) => false
      case N(_) => true
      case Undefined => false
      case S("") => false
      case S(_) => true
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => b.toString
      case N(n) => n.toString
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case B(b) => B(b)
      case N(n) => N(n)
      case S(n) => S(n)
      case Undefined => Undefined
      /* Inductive Cases */

      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case Binary(bop,e1,e2) => bop match {
        case And => if(toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e1)
        case Or => if(toBoolean(eval(env,e1))) eval(env, e1) else eval(env,e2)
        case Eq => (eval(env,e1),eval(env,e2)) match{
          case (N(n1),N(n2)) => B(n1 == n2)
          case (S(s1),S(s2)) => B(s1 == s2)
          case (B(b1),B(b2)) => B(b1 == b2)
          case (B(b),N(n)) => B(toNumber(B(b)) == n)
          case (N(n),B(b)) => B(n == toNumber(B(b)))
          case _ => B(false)
        }
        case Ne => (eval(env,e1),eval(env,e2)) match {
          case (B(b), N(n)) => B(toNumber(B(b)) != n)
          case (N(n), B(b)) => B(n != toNumber(B(b)))
          case _ => B(eval(env,e1)!=eval(env,e2))
        }
        case Plus => (eval(env,e1),eval(env,e2)) match {
          case (S(s1),S(s2)) => S(s1+s2)
          case (S(s1),N(n2)) => S(s1+toStr(N(n2)))
          case (N(n1),S(s2)) => S(toStr(N(n1))+s2)
          case (B(b1),S(s2)) => S(toStr(B(b1))+s2)
          case (S(s1),B(b2)) => S(s1+toStr(B(b2)))
          case (_,_) => N(toNumber(eval(env,e1))+toNumber(eval(env,e2)))
        }
        case Lt => (eval(env,e1),eval(env,e2)) match {
          case (S(s1),S(s2)) => B(s1<s2)
          case (_,_) => B(toNumber(eval(env,e1)) < toNumber(eval(env,e2)))
        }
        case Le => (eval(env,e1),eval(env,e2)) match {
          case (S(s1), S(s2)) => B(s1 <= s2)
          case (_, _) => B(toNumber(eval(env, e1)) <= toNumber(eval(env, e2)))
        }
        case Gt => (eval(env,e1),eval(env,e2)) match {
          case (S(s1), S(s2)) => B(s1 > s2)
          case (_, _) => B(toNumber(eval(env, e1)) > toNumber(eval(env, e2)))
        }
        case Ge => (eval(env,e1),eval(env,e2)) match {
          case (S(s1), S(s2)) => B(s1 >= s2)
          case (_, _) => B(toNumber(eval(env, e1)) >= toNumber(eval(env, e2)))
        }
        case Minus => N(toNumber(eval(env,e1))- toNumber(eval(env,e2)))
        case Times => N(toNumber(eval(env,e1))* toNumber(eval(env,e2)))
        case Div => N(toNumber(eval(env,e1))/ toNumber(eval(env,e2)))
        case Seq => eval(env,e1); eval(env,e2)

      }
      case If(e1, e2, e3) => if(toBoolean(eval(env,e1))) eval(e2) else eval(e3)
      case Unary(uop, e1) => uop match{
        case Neg => N(-toNumber(eval(env,e1)))
        case Not => B(!(toBoolean(eval(env,e1))))
      }
      case Var(x) => lookup(env,x)
      case ConstDecl(x: String, e1, e2) => eval(extend(env, x, eval(env,e1)), e2)
      case _ => throw new UnsupportedOperationException
    }
  }



  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
