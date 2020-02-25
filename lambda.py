class Variable:
	def __init__(self, name):
		self.name = name

	def unpack_saved(self, saved):
		# replace saved variables with their values
		if self in saved:
			return saved[self]
		return self

	def search(self, var):
		# search for a free variable
		return self == var

	def substitute(self, find, replace):
		# x[x := R] => R
		if self == find:
			return replace

		# y[x := R] => y
		return self

	def step(self):
		# running variables does nothing
		return self, False

	def is_eta_equiv(self, other, var_dict = {}):
		# eta equivalent if variables correspond to each other
		return isinstance(other, Variable) and (self == other or self in var_dict and var_dict[self] == other)

	def __eq__(self, other):
		return isinstance(other, Variable) and self.name == other.name

	def __hash__(self):
		return hash(self.name)

	def __repr__(self):
		return '%s' % self.name


class Application:
	def __init__(self, left, right):
		self.left = left
		self.right = right

	def unpack_saved(self, saved):
		# replace saved variables with their values in child nodes
		return Application(self.left.unpack_saved(saved), self.right.unpack_saved(saved))

	def search(self, var):
		# search for a free variable
		return self.left.search(var) or self.right.search(var)

	def substitute(self, find, replace):
		# (M N)[x := R] => (M[x := R] N[x := R])
		return Application(self.left.substitute(find, replace), self.right.substitute(find, replace))

	def step(self):
		# we do one beta reduction at a time so that the step command makes sense

		# beta reduce functions
		if isinstance(self.left, Function):
			return self.left.body.substitute(self.left.arg, self.right), True

		# run left node
		left, changed = self.left.step()
		if changed:
			return Application(left, self.right), True

		# run right node
		right, changed = self.right.step()
		return Application(left, right), changed

	def is_eta_equiv(self, other, var_dict = {}):
		# eta equivalent if child nodes are eta equivalent
		return isinstance(other, Application) \
		   and self.left.is_eta_equiv(other.left, var_dict) and self.right.is_eta_equiv(other.right, var_dict)

	def __eq__(self, other):
		return isinstance(other, Application) and self.left == other.left and self.right == other.right

	def __repr__(self):
		# figure out left parentheses
		if isinstance(self.left, Function):
			left = '(%s)' % self.left
		else:
			left = '%s' % self.left

		# figure out right parentheses
		if isinstance(self.right, Variable):
			right = '%s' % self.right
		else:
			right = '(%s)' % self.right

		# result
		return '%s %s' % (left, right)


class Function:
	def __init__(self, arg, body):
		self.arg = arg
		self.body = body

	def unpack_saved(self, saved):
		# don't do anything if the arg is a saved variable
		if self.arg in saved:
			return self

		# replace saved variables with their values in the body
		return Function(self.arg, self.body.unpack_saved(saved))

	def search(self, var):
		# search for a free variable
		return self.arg != var and self.body.search(var)

	def substitute(self, find, replace):
		# (λx.M)[x := R] => λx.M
		if self.arg == find:
			return self

		# if y is a free variable in R, then
		# (λy.M)[x := R] => λy'.(M[y := y', x := R]) for some y' not a free variable in R

		# find a free variable in R
		arg = self.arg
		while replace.search(arg):
			arg = Variable(arg.name + "'")

		# alpha convert
		if arg != self.arg:
			body = self.body.substitute(self.arg, arg)
		else:
			body = self.body

		# (λy.M)[x := R] => λy.(M[x := R])
		return Function(arg, body.substitute(find, replace))

	def step(self):
		# run the body
		body, changed = self.body.step()
		return Function(self.arg, body), changed

	def is_eta_equiv(self, other, var_dict = {}):
		# other must be a function to even be considered
		if not isinstance(other, Function):
			return False

		# if the arguments are different, check equivalency with the args corresponding to each other
		new_var_dict = var_dict
		if self.arg != other.arg:
			new_var_dict = var_dict.copy()
			new_var_dict[self.arg] = other.arg

		# check equivalency of the body
		return self.body.is_eta_equiv(other.body, new_var_dict)

	def __eq__(self, other):
		return isinstance(other, Function) and self.arg == other.arg and self.body == other.body

	def __repr__(self):
		if isinstance(self.body, Function):
			# group arguments together
			body = ('%s' % self.body).split('.')
			args = body[0][1:]
			return 'λ%s %s.%s' % (self.arg, args, '.'.join(body[1:]))

		# return result without any modifications
		return 'λ%s.%s' % (self.arg, self.body)


def lex(string):
	token = ''

	for c in string:
		# yield special characters
		if c in '().\\λ=':
			if token != '':
				yield token
				token = ''
			yield c
		elif c in ' \t':
			# skip whitespace
			if token != '':
				yield token
				token = ''
		elif c == ';':
			# stop after comments
			if token != '':
				yield token
			return
		else:
			# grow symbol tokens
			token += c

	# yield the last token
	if token != '':
		yield token


def build_application(stack, start_index):
	built = None

	# build the application left to right
	for expr in stack[start_index:]:
		if built is None:
			built = expr
		else:
			built = Application(built, expr)

	# pop everything
	del stack[start_index:]
	return built


def apply_stack(stack):
	# right parentheses pop until a left parenthesis is found
	built = None
	checking_lambda_args = False

	for i in range(len(stack))[::-1]:
		expr = stack[i]

		if checking_lambda_args:
			# between λ and . should be only variables
			if isinstance(expr, Variable):
				built = Function(stack.pop(), built)
			elif expr == '\\' or expr == 'λ':
				# if a function isn't built, then λ. happened
				if not isinstance(built, Function):
					return "Syntax error: '%s' followed by '.'" % expr

				# push the new function to the stack and exit lambda arg mode
				stack.pop()
				stack.append(built)
				built = None
				checking_lambda_args = False
			else:
				# not a valid argument
				return "Syntax error: invalid argument %r" % expr
		elif expr == '(':
			# left parenthesis forces application building
			built = build_application(stack, i + 1)
			return built
		elif expr == '.':
			# enter lambda arg mode
			built = build_application(stack, i + 1)
			stack.pop()
			checking_lambda_args = True
		elif expr == '\\' or expr == 'λ':
			# stray lambdas should not be allowed
			return "Syntax error: unexpected '%s'" % expr

	# checking_lambda_args means that the function being checked was never started
	# ie, a stray dot
	if checking_lambda_args:
		return "Syntax error: unexpected '.'"
	elif built is None:
		return build_application(stack, 0)
	return built


# running mode constants
LAMBDA_MODE_NONE = 0b0000
LAMBDA_MODE_RUN  = 0b0001
LAMBDA_MODE_SET  = 0b0010
LAMBDA_MODE_STEP = 0b0100
LAMBDA_MODE_ERR  = 0b1000


def parse(string):
	stack = []
	inside_lambda = False
	mode = LAMBDA_MODE_NONE
	var_name = None

	for token in lex(string):
		if token in '(':
			# push left parentheses onto the stack
			stack.append(token)
		elif token in '\\λ.':
			# push lambdas and dots onto the stack and change the lambda mode
			stack.append(token)
			inside_lambda = token != '.'
		elif token == ')':
			# apply everything on the stack until the first left parenthesis
			built = apply_stack(stack)

			if isinstance(built, str):
				# some error occured
				return built, LAMBDA_MODE_ERR
			elif len(stack) == 0:
				# no left parenthesis found
				return "Syntax error: unexpected ')'", LAMBDA_MODE_ERR
			else:
				# pop the parenthesis and push the built expression
				stack.pop()
				stack.append(built)
		elif token == 'run':
			# change the mode to run
			if len(stack) == 0 and not (mode & LAMBDA_MODE_STEP):
				mode |= LAMBDA_MODE_RUN
			else:
				return "Syntax error: unexpected 'run'", LAMBDA_MODE_ERR
		elif token == 'step':
			# change the mode to run
			if len(stack) == 0 and not (mode & LAMBDA_MODE_RUN):
				mode |= LAMBDA_MODE_STEP
			else:
				return "Syntax error: unexpected 'run'", LAMBDA_MODE_ERR
		elif token == '=':
			# change the mode to set
			if len(stack) == 1 and isinstance(stack[0], Variable):
				mode |= LAMBDA_MODE_SET
				var_name = stack.pop()
			else:
				return "Syntax error: unexpected '='", LAMBDA_MODE_ERR
		else:
			# push symbols onto stack
			var = Variable(token)
			stack.append(var)

	# apply everything in the stack
	built = apply_stack(stack)

	# check for errors and do last minute processing
	if len(stack) > 0 and not isinstance(built, str):
		# unmatched parenthesis error
		return "Syntax error: unmatched '('", LAMBDA_MODE_ERR
	elif isinstance(built, str):
		# other error
		return built, LAMBDA_MODE_ERR
	elif mode & LAMBDA_MODE_SET:
		if built is None:
			# 'x =' is illegal
			return "Syntax error: unexpected '='", LAMBDA_MODE_ERR
		else:
			# set
			return Application(var_name, built), mode
	else:
		# expression or run
		return built, mode

if __name__ == '__main__':
	import re
	print('Lambda parser and applicator')
	string = None
	saved = {}
	max_iters = 1000

	while True:
		try:
			string = input('> ').strip()
		except:
			print()
			break

		if string == 'exit' or string == 'quit':
			break
		elif string.startswith('setiter'):
			# get the arg for setting the maximum iteration count
			splitted = re.split('\W+', string)

			# must have one argument
			if len(splitted) != 2:
				print('Syntax error: expected one integer argument for setiter')
				continue

			try:
				# set the maximum iteration count
				max_iters = int(splitted[1])
				print('Set the maximum iteration count to %i' % max_iters)
			except:
				print('Syntax error: expected one integer argument for setiter')
			continue
		elif string.startswith('populate'):
			# get the args for populating church hill numbers
			splitted = re.split('\W+', string)

			# must have two arguments
			if len(splitted) != 3:
				print('Syntax error: expected two integer arguments for populate')
				continue

			try:
				# get the start and end
				start = int(splitted[1])
				end = int(splitted[2])
			except:
				print('Syntax error: expected two integer arguments for populate')
				continue

			# λs z.z is zero
			body = Variable('z')
			for i in range(0, end + 1):
				if i >= start:
					# add all the numbers in the specified range as variables
					saved[Variable('%i' % i)] = Function(Variable('s'), Function(Variable('z'), body))

				# successor function; ie, (λn.λs z.s (n s z)) i
				body = Application(Variable('s'), body)

			print('Populated numbers %i to %i' % (start, end))
			continue

		tree, mode = parse(string)

		if tree is None:
			# nothing entered
			continue
		elif mode == LAMBDA_MODE_ERR:
			# error
			print(tree)
			continue

		if mode & LAMBDA_MODE_SET and tree.left in saved:
			# check if variable is already defined
			print('%s is already defined' % tree.left)
			continue

		tree = tree.unpack_saved(saved)

		if mode & (LAMBDA_MODE_RUN | LAMBDA_MODE_STEP):
			# run or step
			running = True
			iter = 0

			try:
				while running and iter < max_iters:
					if (mode & LAMBDA_MODE_STEP):
						# step through execution one beta reduction at a time
						print(tree)
						command = input('!!').strip()

						# commands for halting execution
						if command == 'exit' or command == 'quit':
							raise StopIteration()
						elif command == 'run' or command == 'continue':
							mode ^= LAMBDA_MODE_STEP | LAMBDA_MODE_RUN
					else:
						# count number of iterations
						iter += 1

					# execute
					tree, running = tree.step()

				if iter >= max_iters:
					print('Warning: maximum iterations achieved (use setiter integer or step through execution)')
			except RecursionError:
				print('Error: maximum recursion depth exceeded (try increasing program memory)')
				continue
			except KeyboardInterrupt:
				print('\nExecution halted')
				continue
			except EOFError:
				print('\nExecution halted')
				continue
			except StopIteration:
				print('Execution halted')
				continue

		if mode & LAMBDA_MODE_SET:
			# set
			saved[tree.left] = tree.right
			print('Added %s as %s' % (tree.right, tree.left))
		else:
			# search for eta equivalent functions saved and print them out
			for key in saved:
				if tree.is_eta_equiv(saved[key]):
					print(key)

			# print the final expression
			print(tree)
