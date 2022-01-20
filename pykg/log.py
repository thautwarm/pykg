from loguru import logger

_LINE_FOLD = 50

def warn(s: str):
    if len(s) > _LINE_FOLD:
        logger.warning('\n' + s)
    else:
        logger.warning(s)


def error(s: str):
    if len(s) > _LINE_FOLD:
        logger.error('\n' + s)
    else:
        logger.error(s)

def info(s: str):
    if len(s) > _LINE_FOLD:
        logger.info('\n' + s)
    else:
        logger.info(s)

