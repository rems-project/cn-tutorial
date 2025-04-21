def define_env(env):
    """
    This is the hook for the variables, macros and filters.
    """
    import os

    show_todos = "TUTORIAL_TODOS" in os.environ

    def common(mesg, color):
        "Format a TODO (common)"
        if show_todos:
          return '<span style="color:' + color + '">[[' + mesg + "]]</span>"
        else:
          return ""

    #################################################################
    # These should be suppressed for readers that are not tutorial developers:

    @env.macro
    def todo(mesg):
        "Format a TODO"
        return common(mesg, "red") 

    @env.macro
    def later(mesg):
        "Format a TODO for later"
        return common(mesg, "lightgray") 

    #################################################################
    # These should always be displayed / hidden

    @env.macro
    def hidden(mesg):
        "Format a TODO that should not actually appear right now"
        return ""

    #################################################################
    # Authors and contributors

    authors_fn = os.path.join(env.project_dir, 'AUTHORS')
    with open(authors_fn, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        authors = [l for l in lines if not l.startswith('#')]

    contributors_fn = os.path.join(env.project_dir, 'CONTRIBUTORS')
    with open(contributors_fn, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        contributors = [l for l in lines if not l.startswith('#')]

    # Contributors, not authors
    cna = [a for a in contributors if a not in authors]

    @env.macro
    def latex_authors():
        # NOTE: Software Foundations does not include non-author contributors
        #   in its LaTeX citations. We might want to do the same, in which case
        #   one just has to delete `+ cna`.
        return ' and '.join(authors + cna)

    @env.macro
    def text_authors():
        if len(authors) == 1:
            authors_list = authors[0]
        else:
            authors_list = ', '.join(authors[:-1]) + ', and ' + authors[-1]

        if len(cna) == 1:
            cna_list = cna[0]
        else:
            cna_list = ', '.join(cna[:-1]) + ', and ' + cna[-1]

        return f'{authors_list}, with contributions from {cna_list}'
