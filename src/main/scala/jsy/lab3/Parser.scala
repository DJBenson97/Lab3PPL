/**
 *
 */
package jsy.lab3

import jsy.lab3.ast._
import scala.util.parsing.combinator._
import scala.util.parsing.input.{StreamReader}
import java.io.{InputStreamReader,FileInputStream}
import java.io.InputStream
import java.io.File
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

trait JSTokens extends token.StdTokens {
  case class FloatLiteral(chars: String) extends Token {
    override def toString = chars
  }
}

class Lexer extends lexical.StdLexical with JSTokens {
  override def token: this.Parser[Token] =
    decimal ~ opt(exponent) ^^ {
      case dec ~ exp => FloatLiteral(List(Some(dec), exp).flatten.mkString)
    } |
    super.token
    
  def decimal: this.Parser[String] =
    rep1(digit) ~ opt('.' ~ rep(digit)) ^^ {
      case ws ~ fs =>
        List(Some(ws), fs map { mkList }).flatten.flatten.mkString
    }
  
  def exponent: this.Parser[String] =
    (accept('e') | accept('E')) ~ opt(accept('+') | accept('-')) ~ rep1(digit) ^^ { 
      case exp ~ sign ~ digits =>
        List(Some(List(exp)), sign map { List(_) }, Some(digits)).flatten.flatten.mkString
    }
}

trait TokenParser extends syntactical.StdTokenParsers {
  type Tokens = JSTokens
  val lexical = new Lexer
  
  import lexical.FloatLiteral
  
  def floatLit: this.Parser[String] =
    elem("float", _.isInstanceOf[FloatLiteral]) ^^ (_.chars)
}

object Parser extends TokenParser {
  /* Lexer Set Up */
  lexical.reserved ++= List("jsy", "undefined", "true", "false", "print", "console", "log", "const", "function", "return", "number", "bool", "string", "Undefined", "null", "Null", "interface", "var", "name", "ref", "RegExp")
  lexical.delimiters ++= List("-", "!", ";", ",", "+", "*", "/", "=", "===", "!==", "<", "<=", ">", ">=", "&&", "||", "(", ")", ".", "{", "}", "?", ":", "=>")
  
  /* Helpers */
  def seqExpr(e1: Expr, e2: Expr): Expr = Binary(Seq, e1, e2)
  
  /* EBNF 
   * 
   * prog ::= {stmt}
   * stmt ::= block | decl | ; | expr
   * block ::= '{' prog '}'
   * decl ::= const x = expr
   * expr ::= seq
   * seq ::= cond{,cond}
   * noseq ::= arrow
   * arrow ::= x => noseq | cond
   * cond ::= binary [? cond : cond]
   * binary ::= unary{bop(_)unary}
   * unary ::= uop unary | call
   * call ::=  term{(expr)}
   * term ::= x | n | b | undefined | jsy.print(expr) | (expr)
   */
  
  sealed abstract class PStmt
  case class ExprPStmt(e: Expr) extends PStmt
  case class DeclPStmt(d: Expr => Expr) extends PStmt
  case object EmpPStmt extends PStmt
  
  def prog: this.Parser[Expr] =
    stmts ^^ (s => s(None))
  
  def stmts: this.Parser[Option[Expr] => Expr] =
    rep(stmt) ^^ { (stmts: List[PStmt]) => (body: Option[Expr]) =>
      (stmts foldRight body){
        case (EmpPStmt, eopt) => eopt
        case (ExprPStmt(e), None) => Some(e)
        case (ExprPStmt(e1), Some(e2)) => Some(seqExpr(e1, e2))
        case (DeclPStmt(d), None) => Some(d(Undefined))
        case (DeclPStmt(d), Some(e)) => Some(d(e))
      } match {
        case None => Undefined
        case Some(e) => e
      }
    }

  def stmt: this.Parser[PStmt] =
    block ^^ ExprPStmt |
    decl ^^ DeclPStmt |
    expr ^^ ExprPStmt |
    empty_stmt
  
  def empty_stmt: this.Parser[PStmt] =
    ";" ^^ (_ => EmpPStmt)
    
  def block: this.Parser[Expr] =
    "{" ~> prog <~ "}"
    
  def decl: this.Parser[Expr => Expr] =
    ("const" ~> ident) ~ withpos("=" ~> expr) ^^ {
      case x ~ ((pos,e1)) => ((e2: Expr) => ConstDecl(x, e1, e2) setPos pos)
    }
    
  def expr: this.Parser[Expr] =
    seq
    
  def seq: this.Parser[Expr] =
    noseq ~ withposrep("," ~> noseq) ^^ {
      case e0 ~ es => 
        (es foldRight (None: Option[(Position,Expr)])){
          case ((posi,ei), None) => Some(posi,ei)
          case ((posi,ei), Some((pos,e))) => Some(posi, seqExpr(ei,e) setPos pos)
        } match {
          case None => e0
          case Some((pos,e)) => seqExpr(e0, e) setPos pos
        }
    }
  
  def noseq: this.Parser[Expr] =
    arrow

  def arrow: this.Parser[Expr] =
    (opt("(") ~ ident ~ opt(")")) ~ (withpos("=>" ~> (noseq | funblock))) ^^ {
      case _ ~ x ~ _ ~ ((pos,body)) => Fun(None, x, body) setPos pos
    } |
    cond

  def funblock: this.Parser[Expr] =
    ("{" ~> stmts ~ ret <~ rep(empty_stmt) <~ "}") ^^ {
      case stmts ~ ret => stmts(Some(ret))
    }

  def ret: this.Parser[Expr] =
    "return" ~> expr
    
  def cond: this.Parser[Expr] =
    binary(0) ~ opt(withpos(("?" ~> noseq) ~ (":" ~> noseq))) ^^ {
      case e1 ~ None => e1
      case e1 ~ Some((pos, e2 ~ e3)) => If(e1, e2, e3) setPos pos
    }
    
  val binaryOperators: Vector[List[(String, (Expr, Expr) => Expr)]] = {
    def createBinaryFunction(op: Bop): (Expr, Expr) => Expr =
      { Binary(op, _, _) }
    Vector() ++ List(
      List("||" -> createBinaryFunction(Or)),
      List("&&" -> createBinaryFunction(And)),
      List("===" -> createBinaryFunction(Eq),
           "!==" -> createBinaryFunction(Ne)),
      List("<" -> createBinaryFunction(Lt),
           "<=" -> createBinaryFunction(Le),
           ">" -> createBinaryFunction(Gt),
           ">=" -> createBinaryFunction(Ge)),
      List("+" -> createBinaryFunction(Plus),
           "-" -> createBinaryFunction(Minus)),
      List("*" -> createBinaryFunction(Times),
      	   "/" -> createBinaryFunction(Div))
    )
  }

  def binary(level: Int): this.Parser[Expr] =
    if (level >= binaryOperators.length)
      unary
    else
      binary(level + 1) * bop(level)

  def bop(level: Int): this.Parser[(Expr, Expr) => Expr] = {
    def doBop(opf: (String, (Expr, Expr) => Expr)): this.Parser[(Expr, Expr) => Expr] = {
      val (op, f) = opf
      withpos(op) ^^ { case (pos, _) => ((e1, e2) => f(e1, e2) setPos pos) }
    }
    val bopf0 :: bopfrest = binaryOperators(level)
    (bopfrest.foldLeft(doBop(bopf0)))((acc, bopf) => acc | doBop(bopf))
  }

  def unary: this.Parser[Expr] =
    positioned(uop ~ unary ^^ { case op ~ e => op(e) }) |
    call

  def uop: this.Parser[Expr => Expr] =
    "-" ^^ (_ => (e: Expr) => Unary(Neg, e)) |
    "!" ^^ (_ => (e: Expr) => Unary(Not, e))
    
  def call: this.Parser[Expr] =
    term ~ rep(callop) ^^ { case e0 ~ calls => (calls.foldLeft(e0)){ case (acc, mk) => mk(acc) } }
    
  def callop: this.Parser[Expr => Expr] =
    withpos("(" ~> expr <~ ")") ^^ { case (pos, arg) => (e0 => Call(e0, arg) setPos pos) }

  def term: this.Parser[Expr] =
    positioned(
      ident ^^ (s => Var(s)) |
      floatLit ^^ (s => N(s.toDouble)) |
      stringLit ^^ (s => S(s)) |
      "true" ^^ (_ => B(true)) |
      "false" ^^ (_ => B(false)) |
      "undefined" ^^ (_ => Undefined) |
      ("jsy" ~ "." ~ "print") ~> "(" ~> expr <~ ")" ^^ (e => Print(e)) |
      ("console" ~ "." ~ "log") ~> "(" ~> expr <~ ")" ^^ (e => Print(e)) |
      function
    ) |
    "(" ~> expr <~ ")" |
    "{" ~> "{" ~> prog <~ "}" <~ "}" |
    failure("atomic expression expected")

  def function: this.Parser[Expr] =
    ("function" ~> opt(ident)) ~ ("(" ~> ident <~ ")") ~ funblock ^^ {
      case f ~ x ~ body => Fun(f, x, body)
    }

  def withpos[T](q: => this.Parser[T]): this.Parser[(Position, T)] = this.Parser { in =>
    q(in) match {
      case Success(t, in1) => Success((in.pos,t), in1)
      case ns: NoSuccess => ns
    }
  }
  
  def withposrep[T](q: => this.Parser[T]): this.Parser[List[(Position,T)]] =
    rep(withpos(q))
    
  def withposrep1[T](q: => this.Parser[T]): this.Parser[List[(Position,T)]] =
    rep1(withpos(q))    

  private var parseSource: String = "<source>"
    
  def formatErrorMessage(pos: Position, kind: String, msg: String): String =
    if (pos != NoPosition)
      "%s\n%s:%s:%s: %s\n%s".format(kind, parseSource, pos.line, pos.column, msg, pos.longString)
    else
      "%s\n%s: %s".format(kind, parseSource, msg)
    
  class SyntaxError(msg: String, next: Input) extends Exception {
    override def toString = formatErrorMessage(next.pos, "SyntaxError", msg)
  }
    
  def parseTokens(tokens: lexical.Scanner): Expr = {
    phrase(prog)(tokens) match {
      case Success(e, _) => e
      case NoSuccess(msg, next) => throw new SyntaxError(msg, next)
      case Error(msg, next) => throw new SyntaxError(msg, next)
      case Failure(msg,next) => throw new SyntaxError(msg, next)
    }
  }
    
  /*** External Interface ***/
  
  def formatErrorMessage(e: Expr, kind: String, msg: String): String =
    formatErrorMessage(e.pos, kind, msg)
  
  def parse(s: String): Expr = {
    parseTokens(new lexical.Scanner(s))
  }
  
  def parse(in: InputStream): Expr = {
    val reader = StreamReader(new InputStreamReader(in))
    parseTokens(new lexical.Scanner(reader))
  }
  
  def parseFile(filename: String): Expr = {
    parseSource = filename
    parse(new FileInputStream(filename))
  }
  
  def parseFile(file: File): Expr = {
    parseSource = file.getName
    parse(new FileInputStream(file))
  }

  implicit class StringExpr(s: String) {
    val e = parse(s)
    def a: Expr = e
  }
}
