class Editor {
    private var cursor = 0
    private var text = ""

    private def advance(n: Int = 1): Unit = { cursor += n }
    private def backtrack(n: Int = 1): Unit = { cursor -= n }

    private def end(): Int = {
      if (text.length == 0)
        return 0
      return text.length - 1
    }

    // Deletes the character pointed by the cursor
    def x(): Unit = {
      // Don't do anything if the text is empty
      if (text.length == 0)
        return

      // Move back if the cursor is at the end of the text,
      // otherwise stay still
      if (cursor == end()) {
        text = text.substring(0, cursor)
        backtrack()
      } else {
        text = text.substring(0, cursor) + text.substring(cursor + 1)
      }
    }

    // Deletes from the character pointed by the cursor (included) to the next space (excluded) or to the end of the line
    def dw(): Unit = {
      val from = cursor
      val to = text.indexOf(" ", from + 1)

      // If there are no spaces after the cursor delete the rest of the line and move back
      if (to == -1) {
        text = text.substring(0, from)
        backtrack()
      } else {
        // Delete from the cursor to the next space and stay still
        text = text.substring(0, from) + text.substring(to)
      }
    }

    // Adds a new character C after the character pointed by the cursor and moves the cursor to C
    def i(ch: Char): Unit = {
      if(text.length == 0) {
        text += ch
      } else{
        text = text.substring(0, cursor + 1) + ch + text.substring(cursor + 1)
        advance()
      }
     }

    // Adds a new word W followed by a blank space after the character pointed by the cursor and moves the cursor to the blank space
    def iw(word: String): Unit = {
      val addition = word + " "

      if(cursor == end())
        text += addition
      else
        text = text.substring(0, cursor + 1) + addition + text.substring(cursor + 1)

      advance(addition.length)
    }

    // Moves the cursor n characters to the right from the current position
    def l(n: Int = 1): Unit = {
      // Don't do anything if the cursor is at the end
      if (cursor == end())
        return

      // Don't move the cursor further than the length of the text
      if(n >= end() - cursor)
        advance(end() - cursor)
      else
        advance(n)
    }

    // Moves the cursor n characters to the left from the current position
    def h(n: Int = 1): Unit = {
      // Don't do anything if the cursor is at beginning
      if (cursor == 0)
        return

      // Don't move the cursor further than 0
      if(n >= cursor)
        backtrack(cursor)
      else
        backtrack(n)
    }

    override def toString(): String = {
      if (cursor < 10)
        return s"[0$cursor]: |$text|"
      return s"[$cursor]: |$text|"
    }
  }

  object Editor {
    def main(args: Array[String]): Unit = {
      val editor = new Editor()

      "This is a test!! ".foreach(x => editor.i(x))
      println(editor) // [16]: |This is a test!! |

      editor.x()
      editor.x()
      println(editor) // [14]: |This is a test!|

      editor.iw(" Another test")
      println(editor) // [28]: |This is a test! Another test |

      editor.h(100)
      editor.l(9)
      editor.iw("new")
      println(editor) // [13]: |This is a new test! Another test |

      editor.dw()
      println(editor) // [13]: |This is a test! Another test |
    }
  }

// scalac Editor.scala && scala Editor
