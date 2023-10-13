## Script to easily verify packages of SCION

import argparse
from scion import defs, router, path_scion

def cli_parser():
    # create the top-level parser
    parser = argparse.ArgumentParser(prog='scion-verify')
    parser.set_defaults(func=lambda _: parser.print_help())
    subparsers = parser.add_subparsers()

    parser_router = subparsers.add_parser('router', help='verify the border router')
    parser_router.set_defaults(func=verify_router)

    parser_path_scion = subparsers.add_parser('pscion', help='verify the path/scion package')
    parser_path_scion.set_defaults(func=verify_path_scion)

    return parser

def verify_router(_):
    defs.call_gobra(router.dataplane_cfg)

def verify_path_scion(_):
    defs.call_gobra(path_scion.path_cfg)

if __name__ == "__main__":
    parser = cli_parser()
    args = parser.parse_args()
    args.func(args)
