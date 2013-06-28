class TestGenerator(object):
    """Base class for test case generators."""

    def __init__(self, test_file_name):
        """Initialize the test generator.

        test_file_name is the file name for test output.  The subclass
        may derive other file names from this.
        """
        self.__callset = self.__model = None

    def begin_call_set(self, callset):
        """Handle the beginning of a call set.

        callset is a list of method objects.  This saves this
        information so information about the current callset can be
        queried later.
        """
        self.__callset = callset

    @property
    def callset_names(self):
        """A list of string names of the methods in the current call set."""
        return [c.__name__ for c in self.__callset]

    def get_call_args(self, callno):
        """Return the arguments struct for the callno'th call."""
        var_name = (chr(ord('a') + callno) + "." +
                    self.__callset[callno].__name__)
        return self.__model[var_name]

    def on_model(self, result, model):
        """Generate a test for a single code path and concrete assignment.

        result is the simsym.SymbolicApplyResult representing this
        code path.  model is the simsym.Model object giving the
        concrete assignment.

        The default implementation of this method saves the result and
        model for methods that look up information from them.
        Subclasses should override this method to process each model,
        but the implementation must first call the superclass method.
        """
        self.__model = model

    def end_call_set(self):
        """Handle the end of a call set."""
        self.__callset = None

    def finish(self):
        """Finish test generation.

        The default implementation of this method does nothing."""
        pass
