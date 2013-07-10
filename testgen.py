import simsym

class TestGenerator(object):
    """Base class for test case generators.

    The methods of this class will be invoked as symbolic execution
    and model enumeration proceed in the following order:
      (begin_call_set (begin_path on_model+ end_path)* end_call_set)* finish
    Subclasses may override any of these methods, but should always
    call the superclass method.
    """

    def __init__(self, test_file_name):
        """Initialize the test generator.

        test_file_name is the file name for test output.  The subclass
        may derive other file names from this.
        """
        self.__callset = self.__result = self.__model = None

    def begin_call_set(self, callset):
        """Handle the beginning of a call set.

        callset is a list of method objects representing the methods
        being tested for commutativity.

        Execution of the call set will yield zero or more code paths.
        """
        self.__callset = callset

    @property
    def callset_names(self):
        """A list of string names of the methods in the current call set."""
        return [c.__name__ for c in self.__callset]

    def get_result(self, callno, permno=0):
        """Return the result for the callno'th call.

        This may contain unevaluated symbolic expressions.  These
        should be passed to self.eval to evaluate them to concrete
        values.
        """
        return self.__result.value.results[permno][callno]

    def eval(self, expr):
        """Evaluate a symbolic expression.

        This isn't necessary for things retrieved from the model such
        as call arguments and state since those are automatically
        evaluated, but result values from model methods require
        explicit evaluation.
        """
        if isinstance(expr, simsym.Symbolic):
            # This is used for result values, so don't track explicit
            # evaluations or we'll try to enumerate result values
            # (testgen should never use a result value that isn't
            # completely deterministic, but IsomorphicMatch will still
            # try to destructure any tracked evaluations)
            return self.__model._eval(expr, track=False)
        return expr

    def get_call_args(self, callno):
        """Return the arguments struct for the callno'th call."""
        var_name = (chr(ord('a') + callno) + "." +
                    self.__callset[callno].__name__)
        return self.__model[var_name]

    def begin_path(self, result):
        """Handle the beginning of a code path.

        result is the simsym.SymbolicApplyResult representing this
        code path.

        The code path will have one or more models that satisfy its
        path condition.
        """
        self.__result = result

    def on_model(self, model):
        """Handle a concrete assignment for the current code path.

        model is the simsym.Model object giving the concrete
        assignment.

        This method may be called more than once for a single code
        path.  Each call's model will differ in the value of at least
        one expression that was evaluated by past calls to on_model.
        """
        self.__model = model

    def end_path(self):
        """Handle the end of a code path."""
        self.__result = None

    def end_call_set(self):
        """Handle the end of a call set."""
        self.__callset = None

    def finish(self):
        """Finish test generation.

        The default implementation of this method does nothing."""
        pass

class CodeWriter(object):
    def __init__(self, fp=None):
        self.__fp = fp
        if fp is None:
            self.__blocks = []

    def __call__(self, *blocks):
        if self.__fp:
            self.__fp.write('\n'.join(map(str, blocks)) + '\n')
            self.__fp.flush()
        else:
            self.__blocks.extend(blocks)
        return self

    def __repr__(self):
        return 'CodeWriter(%r)' % self.__fp

    def __str__(self):
        if self.__fp:
            return repr(self)
        return '\n'.join(map(str, self.__blocks))

    def indent(self, by="  "):
        indented = by + str(self).replace('\n', '\n' + by)
        return CodeWriter()(indented)
