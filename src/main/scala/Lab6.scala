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
      case Success(r, next) => println("Union ",r,next.first); {
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


    def intersect(next: Input): ParseResult[RegExpr] = concat(next) match{
      case Success(r,next) => println("intersect ",r,next.first); {
        def intersections(acc: RegExpr, next:Input): ParseResult[RegExpr] =
          if(next.atEnd) Success(acc,next)
          else (next.first, next.rest) match {
            case('&',next) => concat(next) match{
              case Success(r,next) => intersections(RIntersect(acc,r), next)
              case _ => Failure("expected concat", next)
            }
            case _ => Success(acc,next)
          }
        intersections(r,next)
      }
      case _ => Failure("expected concat", next)
    }

    def concat(next: Input): ParseResult[RegExpr] = not(next) match{
      case Success(r,next) => println("Concat ",r,next.first); {
        def concats(acc: RegExpr, next:Input): ParseResult[RegExpr] =
          if(next.atEnd) Success(acc,next)
          else (next.first, next.rest) match {
            case (c, _) if(!myDel.contains(c)) => not(next) match{
              case Success(r, next) => concats(RConcat(acc,r),next)
              case _ => Failure("bad", next)
            }
            //TODO find better way to ignore '|', '&', '~',')'
            case _ => Success(acc, next)
          }
        concats(r,next)
      }
      case _ => Failure("expected something", next)
    }

    def not(next: Input): ParseResult[RegExpr] = star(next) match {
      case Success(r,next) => println("Not ",r,next.first);
        if (next.atEnd) Success(r,next)
        else (next.first, next.rest) match {
          case ('~',next) => star(next) match{
            case Success(r,next) => Success(RNeg(r),next)
            case _ => Failure("Expected atom",next)
          }
          case _ => Success(r, next)
        }
      case _ => Failure("Bad", next)
    }

    def star(next: Input): ParseResult[RegExpr] = atom(next) match{
      case Success(r, next) => println("Star ",r,next.first); {
        def stars(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('*', next) => stars(RStar(acc),next)
            case ('+', next) => stars(RPlus(acc),next)
            case ('?', next) => stars(ROption(acc),next)
            case _ => Success(acc, next)
          }
        stars(r, next)
     }
      case _ => Failure("expected atom", next)
    }

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')
    val myDel = Set('|', '&', '~',')')

    def atom(next: Input): ParseResult[RegExpr] =
      if (next.atEnd) Failure("expected atom", next)
      else (next.first, next.rest) match {
        case ('!', next) => Success(RNoString, next)
        case ('#', next) => Success(REmptyString, next)
        case ('.', next) => Success(RAnyChar, next)
        case ('(', next) => re(next) match {
          case Success(r, next) => (next.first, next.rest) match {
            case (')', next) => Success(r, next)
            case _ => Failure("unmatched (", next)
          }
          case fail => fail
        }
        case ('~',next) => star(next) match{
          case Success(r,next) => Success(RNeg(r),next)
          case _ => Failure("Expected atom",next)
        }
        case (c, next) if (!delimiters.contains(c)) => Success(RSingle(c), next)
        case _ => Failure("expected atom", next)
      }
    

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
        case (RNoString, _) => false
        case (REmptyString, _) => sc(chars)
        case (RSingle(c1), Nil) => false
        case (RSingle(c1), h::t) => h == c1 && sc(t)
        case (RConcat(re1, re2), _) => test(re1, chars, {rest => test(re2, rest, sc)})
        case (RUnion(re1, re2), _) => test(re1, chars, sc) || test(re2, chars, sc)
        case (RStar(re1), _) => sc(chars) || test(re1, chars,
          {rest => if (chars == rest) false else test(re, rest, sc)})

        /* Extended Operators */
        case (RAnyChar, Nil) => false
        case (RAnyChar, h::t) => sc(t)
        case (RPlus(re1), _) => test(re1, chars, {rest => test(RStar(re1), rest, sc)})
        case (ROption(re1), _) => sc(chars) || test(re1, chars, sc)
        
        /***** Extra Credit Cases *****/
        case (RIntersect(re1, re2), _) => test(re1, chars, sc) && test(re2, chars, sc)
        case (RNeg(re1), _) => !test(re1, chars, {rest => rest.isEmpty}) || (sc(chars) && !chars.isEmpty)
      }
    }
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

  var useReferenceRegExprParser = false /* set to true to use the reference parser */
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
