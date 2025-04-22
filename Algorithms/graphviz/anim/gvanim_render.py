# from __future__ import absolute_import

from subprocess import Popen, PIPE, STDOUT, call
from multiprocessing import Pool, cpu_count

def _render( params ):
	path, fmt, size, graph = params
	with open( path , 'w' ) as out:
		cmd_render = [ 'dot',  
			'-Gsize=1,1!', 
			'-Gdpi={}'.format( size ), 
			'-T', fmt ]
		print(cmd_render) # DEBUG
		pipe = Popen(cmd_render , stdout = out, stdin = PIPE, stderr = None )
		pipe.communicate( input = graph.encode() )
	return path

def render( graphs, basename, fmt = 'png', size = 320 ):
	print(graphs, basename, fmt) # DEBUG
	try:
		_map = Pool( processes = cpu_count() ).map
	except NotImplementedError:
		_map = map
	print(_map) # DEBUG
	return _map( _render, [ ( '{}_{:03}.{}'.format( basename, n, fmt ), fmt, size, graph ) for n, graph in enumerate( graphs ) ] )

def gif( files, basename, delay = 100, size = 320 ):
	for file in files:
		cmd_mogrify = [ 'mogrify', '-gravity', 'center', '-background', 'white', '-extent', str(size), file ]
		print(cmd_mogrify) # DEBUG
		call(cmd_mogrify)
	
	cmd = [ 'convert', '-dispose', '3' ]
	for file in files:
		cmd.extend( ( '-delay', str( delay ), file ) )
	cmd.extend( ('-write', basename + '.gif') )
	print( cmd ) # DEBUG
	call( cmd, shell=False )