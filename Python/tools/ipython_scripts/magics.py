from IPython.core.magic import Magics, magics_class, cell_magic
from IPython import get_ipython

@magics_class
class ForceContinue(Magics):

  @cell_magic
  def force_continue(self, line, cell):
    try:
      # self.shell.ex(cell)
      get_ipython().run_cell(cell)
    except Exception as e:
      print("FORCE CONTINUE")
    else:
      pass