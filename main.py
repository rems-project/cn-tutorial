def define_env(env):
    """
    This is the hook for the variables, macros and filters.
    """

    def common(mesg, color):
        "Format a TODO (common)"
        return "<span style=\"color:" + color + "\">[[" + mesg + "]]</span>"

    @env.macro
    def todo(mesg):
        "Format a TODO"
        return common(mesg, "red")

    @env.macro
    def later(mesg):
        "Format a TODO for later"
        return common(mesg, "lightgray")

        
