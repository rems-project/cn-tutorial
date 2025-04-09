def define_env(env):
    """
    This is the hook for the variables, macros and filters.
    """
    import os

    show_todos = "TUTORIAL_TODOS" in os.environ

    def common(mesg, color):
        "Format a TODO (common)"
        return '<span style="color:' + color + '">[[' + mesg + "]]</span>"

    #################################################################
    # These should be suppressed for readers that are not tutorial developers:

    @env.macro
    def todo(mesg):
        "Format a TODO"
        return common(mesg, "red") if show_todos else ""

    @env.macro
    def later(mesg):
        "Format a TODO for later"
        return common(mesg, "lightgray") if show_todos else ""

    #################################################################
    # These should always be displayed / hidden

    @env.macro
    def hidden(mesg):
        "Format a TODO that should not actually appear right now"
        return ""

    @env.macro
    def verifmarkername():
        return '<span style="color:black">(V)</span>'

    @env.macro
    def verifmarker(title):
        "format a title with a marker that it is a verification chapter"
        return verifmarkername() + " " + title
