from mkdocs.structure.nav import Navigation
from mkdocs.structure.pages import Page
from typing import Union
from mkdocs.utils.templates import TemplateContext

def on_page_markdown(markdown: str, page: Page, **kwargs) -> Union [str, None]:
    if page.meta.get('flow') != 'Verification':
        return markdown

    # Split the markdown into lines
    lines = markdown.splitlines()

    # Replace the first line starting with '#'
    for i, line in enumerate(lines):
        line = line.lstrip()
        if line.startswith('#'):
            lines[i] = f'# *{line[1:].lstrip()}*'
            break

    # Join the lines back into a single string
    markdown = '\n'.join(lines)

    return markdown


def on_page_context(context: TemplateContext, **kwargs) -> Union [TemplateContext, None]:
    nav: Navigation = context.get('nav')  # type: ignore

    for page in nav.pages:
        if page.meta.get('flow') == 'Verification':
            page.title = f'<i>{page.title}</i>'

    return context
