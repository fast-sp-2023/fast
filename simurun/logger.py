import logging 
import re
import sty
import os

ATTENTION = 15

class ColorFormatter(logging.Formatter):
    def format(self, record):
        res = super(ColorFormatter, self).format(record)
        if record.levelno >= logging.ERROR:
            res = sty.fg.red + sty.ef.bold + res + sty.rs.all
        elif record.levelno == logging.WARNING:
            res = sty.fg.yellow + res + sty.rs.all
        elif record.levelno == ATTENTION:
            res = sty.fg.green + sty.ef.bold + res + sty.rs.all
        return res

class NoColorFormatter(logging.Formatter):
    def format(self, record):
        res = super(NoColorFormatter, self).format(record)
        res = re.sub(r'\x1b\[[0-9;]*[a-zA-Z]', '', res)
        return res

def create_logger(name, output_type="file", level=logging.DEBUG, file_name='run_log.log'):
    """
    we can choose this is a file logger or a console logger
    for now, we hard set the log file name to be run_log.log

    Args:
        name: the name of the logger
        log_type: choose from file or console

    Return:
        the created logger
    """
    logger = logging.getLogger(name)

    for handler in list(logger.handlers):
        logger.removeHandler(handler)

    file_handler = logging.FileHandler(filename=file_name)
    file_handler.setFormatter(NoColorFormatter())
    stream_handler = logging.StreamHandler()
    if os.name == 'nt': # Windows
        stream_handler.setFormatter(NoColorFormatter())
    else:
        stream_handler.setFormatter(ColorFormatter())

    logger.setLevel(level)

    if output_type == "file":
        logger.addHandler(file_handler)
    elif output_type == "console":
        logger.addHandler(stream_handler)

    return logger
