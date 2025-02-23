# Defining custom magics
# https://ipython.readthedocs.io/en/stable/config/custommagics.html

from .magics import ForceContinue
from IPython import get_ipython
from IPython.core.magic import register_cell_magic

def load_ipython_extension(ipython):
  ipython.register_magics(ForceContinue)

@register_cell_magic
def cont(line, cell):
  try:
    get_ipython().run_cell(cell)
  except Exception as e:
    print("SKIP")
  finally:
    pass