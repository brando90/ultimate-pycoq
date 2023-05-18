"""
pycoq methods to interact with logging module
"""


import logging

import pycoq.config

# FORMATTER = '--> %(asctime)s - %(process)d - %(name)s - %(levelname)s - %(message)s ----'
# https://stackoverflow.com/questions/533048/how-to-log-source-file-name-and-line-number-in-python
# FORMATTER = '--> [%(asctime)s] p%(process)s {%(pathname)s:%(lineno)d} %(levelname)s - %(message)s'
FORMATTER ='{%(pathname)s:%(lineno)d} %(levelname)s: %(message)s'

def logging_level(a: int):
    ''' returns logging level '''
    return {1: logging.CRITICAL,
            2: logging.ERROR,
            3: logging.WARNING,
            4: logging.INFO,
            5: logging.DEBUG}[a]

def config_logging():
    """Configures python's logging module to print to stdout and logging file."""
    logging.basicConfig(
        format=FORMATTER,
        level=logging_level(pycoq.config.get_log_level()),
        handlers=[
            logging.FileHandler(pycoq.config.get_log_filename()),
            # logging.StreamHandler()
        ]
    )
    
# def debug(msg: str):
#     # print(f'--> logging.debug: {msg=}')
#     logging.debug(msg)
#
# def info(msg: str):
#     # print(f'--> logging.info: {msg=}')
#     logging.info(msg)
#
# def warning(msg: str):
#     # print(f'--> logging.warning: {msg=}')
#     logging.warning(msg)
#
# def error(msg: str):
#     # print(f'--> logging.error: {msg=}')
#     logging.error(msg)
#
# def critical(msg: str):
#     # print(f'--> logging.critical: {msg=}')
#     logging.critical(msg)


config_logging()


