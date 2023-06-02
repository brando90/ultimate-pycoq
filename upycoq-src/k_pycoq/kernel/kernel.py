"""
Defines a kernel interface for Coq. This file outlines the main entry point for interacting with Coq.
"""


class AbstractKernel:

    def __init__(self):
        pass

    async def __aenter__(self):
        """starts kernel"""
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc, tb):
        """closes kernel"""
        await self.terminate()

    async def start(self):
        """starts kernel"""
        pass

    async def terminate(self):
        """closes kernel"""
        pass

    async def add(self, statement: str):
        """adds statement to kernel"""
        pass

    async def query(self, statement: str):
        """queries statement to kernel"""
        pass
