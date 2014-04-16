import jsy.lab6.JsyInterpreter
import jsy.lab6.JsyParser

object Lab6 extends jsy.util.JsyApplication {
  import jsy.lab6.ast._
  
  /*
   * CSCI 3155: Lab 6
   * Dominic Tonozzi and Matthias Sainz
   * 
   * Collaborators: Jacob Resman
   */

  /*** Regular Expression Parsing ***/
  import scala.util.parsing.combinator.Parsers
  import scala.util.parsing.input.Reader
  import scala.util.parsing.input.CharSequenceReader

  /* We define a recursive decent parser for regular expressions in
   * RegExprParser.
   * 
   * We derive RegExprParser from Parsers in the Scala library to make
   * use of it's handing of input (Input) and parsing results
   * (ParseResult).
   * 
   * The Parsers trait is actually a general purpose combinator parser
   * library that we will not use.
   * 
   * Grammar
   * 
   *   re ::= union
   *   union ::= intersect {| intersect}
   *   intersect ::= concat {& concat}
   *   concat ::= not {not}
   *   not ::= ~ not | star
   *   star ::= atom {*|+|?}
   *   atom ::= ! | # | c | . | ( re )
   * 
   */
  object RegExprParser extends Parsers {
    type Elem = Char

    /* The following items are the relevant pieces inherited from Parsers
     * 
     * type Input = Reader[Elem]
     * sealed abstract class ParseResult[+T] {
     *   val next: Input
     *   def map[U](f: T => U): ParseResult[U]
     * }
     * case class Success[+T](result: T, next: Input) extends ParseResult[T]
     * case class Failure(next: Input) extends ParseResult[Nothing]
     */
    
    def re(next: Input): ParseResult[RegExpr] = union(next)

    def union(next: Input): ParseResult[RegExpr] = intersect(next) match {
      case Success(r, next) => {
        def unions(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('|', next) => intersect(next) match {
              case Success(r, next) => unions(RUnion(acc, r), next)
              case _ => Failure("expected intersect", next)
            }
            case _ => Success(acc, next)
          }
        unions(r, next)
      }
      case _ => Failure("expected intersect", next)
    }

    def intersect(next: Input): ParseResult[RegExpr] = throw new UnsupportedOperationException

    def concat(next: Input): ParseResult[RegExpr] = throw new UnsupportedOperationException

    def not(next: Input): ParseResult[RegExpr] = throw new UnsupportedOperationException

    def star(next: Input): ParseResult[RegExpr] = throw new UnsupportedOperationException

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')

    def atom(next: Input): ParseResult[RegExpr] = throw new UnsupportedOperationException
    

    /* External Interface */
    
    def parse(next: Input): RegExpr = re(next) match {
      case Success(r, next) if (next.atEnd) => r
      case Success(_, next) => throw new SyntaxError("remaining input", next.pos)
      case Failure(msg, next) => throw new SyntaxError(msg, next.pos)
    }

    def parse(s: String): RegExpr = parse(new CharSequenceReader(s))
  } 
  

  /*** Regular Expression Matching ***/
  
  def retest(re: RegExpr, s: String): Boolean = {
    def test(re: RegExpr, chars: List[Char], sc: List[Char] => Boolean): Boolean = {
      (re, chars) match {
        /* Basic Operators */
        case (RNoString, _) => false //Fucking hack because this will never show up.
        case (REmptyString, _) => chars.isEmpty
        case (RSingle(c1), chars) => chars.length == 1 &&
          c1 == chars.head
        case (RConcat(re1, re2), _) => chars.length > 0 &&
          test(re1, List(chars.head), sc) && test(re2, chars.tail, sc)
        case (RUnion(re1, re2), _) => test(re1, chars, sc) || test(re2, chars, sc)
        case (RStar(re1), _) => {
          println(chars)
          def stretch(re:RegExpr, h: List[Char], t: List[Char]): (Boolean, List[Char]) = t match {
            case Nil => (test(re1, h, sc), Nil)
            case _ => {
              val (pass, rest) = (test(re, h, sc), t)
              if (pass) (pass, rest) else stretch(re, h:+t.head, t.tail)
            }
          }
          sc(chars) || {
            val (pass, rest) = stretch(re, List(chars.head), chars.tail)
            pass && test(re, rest, sc)
            //Vulnerability here for (aaaa).match(/(aa)*/)
            //Also runs in like n^5 time
          }
        }

        /* Extended Operators */
        case (RAnyChar, _) => chars.length == 1
        case (RPlus(re1), _) => chars.length > 0 &&
          test(re1, List(chars.head), sc) && (sc(chars.tail) || test(RPlus(re1), chars.tail, sc))
        case (ROption(re1), _) => sc(chars) || test(re1, chars, sc)
        
        /***** Extra Credit Cases *****/
        case (RIntersect(re1, re2), _) => test(re1, chars, sc) && test(re2, chars, sc)
        case (RNeg(re1), _) => !test(re1, chars, sc)
      }
    }
    //println(s);
    //println(re);
    test(re, s.toList, { chars => chars.isEmpty })
  }
  
  
  /*** JavaScripty Interpreter ***/

  /* This part is optional and only for fun.
   * 
   * If you want your own complete JavaScripty interpreter, you can copy your
   * Lab 5 interpreter here and extend it for the Lab 6 constructs.
   * 
   * By default, a reference JavaScripty interpreter will run using your
   * regular expression tester.
   */
  object MyInterpreter extends jsy.lab6.Interpreter {
    /* Type checking. */
    def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ =
      throw new UnsupportedOperationException
    
    /* A small-step transition. */
    def stepre(retest: (RegExpr, String) => Boolean)(e: Expr): DoWith[Mem, Expr] = {
      def step(e: Expr): DoWith[Mem, Expr] = {
        require(!isValue(e), "stepping on a value: %s".format(e))
        throw new UnsupportedOperationException
      }
      step(e)
    }
  }


  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.

  var useReferenceRegExprParser = true /* set to true to use the reference parser */
  var useReferenceJsyInterpreter = true /* set to false to use your JavaScripty interpreter */

  this.flagOptions = this.flagOptions ++ List(
    ("ref-reparser", jsy.util.options.SetBool(b => useReferenceRegExprParser = b, Some(b => useReferenceRegExprParser == b)), "using the reference regular expression parser"),
    ("ref-jsyinterp", jsy.util.options.SetBool(b => useReferenceJsyInterpreter = b, Some(b => useReferenceJsyInterpreter == b)), "using the reference JavaScripty interpreter")
  )

  // Select the interpreter to use based on the useReferenceJsyInterpreter flag
  val interpreter: jsy.lab6.Interpreter =
    if (useReferenceJsyInterpreter) jsy.lab6.JsyInterpreter else MyInterpreter
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = interpreter.typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = JsyParser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    val step: Expr => DoWith[Mem, Expr] = interpreter.stepre(retest)
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(memempty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }
  
  // Select the parser to use based on the useReferenceRegExprParser flag
  def parser: JsyParser =
    if (useReferenceRegExprParser) new JsyParser else new JsyParser(RegExprParser.parse)

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      if (useReferenceRegExprParser) println("Parsing with reference RegExpr parser ...")
      else println("Parsing with your RegExpr parser ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val t = inferType(expr)
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }
  
}
